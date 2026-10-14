-- Prove2me | solution 1 for LeightonRao.Uniform.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T22:46:20.387709+00:00
-- url     : https://prove2.me/submissions/78dcfc37-5ecb-4b08-8b3f-1e101cd1e4dc

-- Complete checked reconstruction of the native uniform multicommodity flow-cut theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_LeightonRao_Uniform_Flow
import Mathlib


-- Begin GenericMetric

open scoped BigOperators
namespace LeightonRao.Uniform.Proof

structure FiniteMetric (V : Type) where
  d : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ d u v
  symm : ∀ u v, d u v = d v u
  self : ∀ u, d u u = 0
  triangle : ∀ u v w, d u w ≤ d u v + d v w

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def metricMass (d : FiniteMetric V) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, d.d u v

noncomputable def metricWeight (N : Network V) (d : FiniteMetric V) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, N.C u v * d.d u v

end LeightonRao.Uniform.Proof
-- End GenericMetric

-- Begin ArcBasic

open scoped BigOperators
namespace LeightonRao.Uniform.Proof

abbrev ArcArray (V : Type) := (V × V) → (V × V) → ℝ
abbrev DivArray (V : Type) := (V × V) → V → ℝ

variable {V : Type} [Fintype V]

noncomputable def arcLoad (f : ArcArray V) (i j : V) : ℝ :=
  ∑ st, (f st (i,j) + f st (j,i))

noncomputable def arcDiv (f : ArcArray V) : DivArray V :=
  fun st v => (∑ j, f st (v,j)) - ∑ j, f st (j,v)

def ArcFeasible (N : Network V) (f : ArcArray V) : Prop :=
  (∀ st ij, 0 ≤ f st ij) ∧ (∀ s ij, f (s,s) ij = 0) ∧
    ∀ i j, arcLoad f i j ≤ N.C i j

noncomputable def targetDiv [DecidableEq V] (lam : ℝ) : DivArray V :=
  fun st v => lam * uniformDemand st.1 st.2 *
    ((if v = st.1 then 1 else 0) - (if v = st.2 then 1 else 0))

noncomputable def divPair (p q : DivArray V) : ℝ :=
  ∑ st, ∑ v, p st v * q st v

lemma arcFeasible_zero (N : Network V) : ArcFeasible N 0 := by
  refine ⟨by simp, by simp, ?_⟩
  intro i j
  simpa [arcLoad] using N.C_nonneg i j

lemma arcFeasible_coord_le {N : Network V} {f : ArcArray V}
    (hf : ArcFeasible N f) (st ij : V × V) : f st ij ≤ N.C ij.1 ij.2 := by
  classical
  have h1 : f st ij ≤ f st (ij.1,ij.2) + f st (ij.2,ij.1) := by
    simpa using (le_add_of_nonneg_right (a := f st ij) (hf.1 st (ij.2,ij.1)))
  exact h1.trans ((Finset.single_le_sum (fun x _ => add_nonneg (hf.1 x _) (hf.1 x _))
    (Finset.mem_univ st)).trans (hf.2.2 ij.1 ij.2))

noncomputable def arcDivLinear : ArcArray V →ₗ[ℝ] DivArray V where
  toFun := arcDiv
  map_add' f g := by ext st v; simp [arcDiv, Finset.sum_add_distrib]; ring
  map_smul' a f := by ext st v; simp [arcDiv, Finset.mul_sum, mul_sub]

lemma flow_of_arc [DecidableEq V] {N : Network V} {f : ArcArray V} {lam : ℝ}
    (hf : ArcFeasible N f) (hd : arcDiv f = targetDiv lam) :
    IsConcurrentFlow N uniformDemand (fun s t i j => f (s,t) (i,j)) lam := by
  refine ⟨fun s t i j => hf.1 (s,t) (i,j), ?_, fun s i j => hf.2.1 s (i,j), ?_⟩
  · intro s t _ v
    exact congrFun (congrFun hd (s,t)) v
  · intro i j
    simpa [arcLoad, Fintype.sum_prod_type] using hf.2.2 i j

lemma divPair_arcDiv (p : DivArray V) (f : ArcArray V) :
    divPair p (arcDiv f) = ∑ st, ∑ i, ∑ j, f st (i,j) * (p st i - p st j) := by
  unfold divPair arcDiv
  apply Finset.sum_congr rfl
  intro st _
  simp_rw [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => p st i * f st (j,i))]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

end LeightonRao.Uniform.Proof
-- End ArcBasic

-- Begin ArcTopology

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V]

lemma isClosed_arcFeasible (N : Network V) : IsClosed {f : ArcArray V | ArcFeasible N f} := by
  simp only [ArcFeasible, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun st => isClosed_iInter fun ij => ?_).inter
    ((isClosed_iInter fun s => isClosed_iInter fun ij => ?_).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => ?_))
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_le (by unfold arcLoad; fun_prop) continuous_const

lemma isCompact_arcFeasible (N : Network V) : IsCompact {f : ArcArray V | ArcFeasible N f} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ArcArray V) (fun _ ij => N.C ij.1 ij.2))).of_isClosed_subset
    (isClosed_arcFeasible N)
  intro f hf
  exact ⟨hf.1, fun st ij => arcFeasible_coord_le hf st ij⟩

lemma convex_arcFeasible (N : Network V) : Convex ℝ {f : ArcArray V | ArcFeasible N f} := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro st ij
    exact add_nonneg (mul_nonneg ha (hf.1 st ij)) (mul_nonneg hb (hg.1 st ij))
  · intro s ij
    change a * f (s,s) ij + b * g (s,s) ij = 0
    rw [hf.2.1 s ij, hg.2.1 s ij]; ring
  · intro i j
    have h1 := mul_le_mul_of_nonneg_left (hf.2.2 i j) ha
    have h2 := mul_le_mul_of_nonneg_left (hg.2.2 i j) hb
    have he : arcLoad (a • f + b • g) i j = a * arcLoad f i j + b * arcLoad g i j := by
      simp only [arcLoad, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [show ∀ st : V × V, a * f st (i,j) + b * g st (i,j) +
        (a * f st (j,i) + b * g st (j,i)) =
        a * (f st (i,j) + f st (j,i)) + b * (g st (i,j) + g st (j,i)) by intros; ring]
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    rw [he]
    calc
      _ ≤ a * N.C i j + b * N.C i j := add_le_add h1 h2
      _ = N.C i j := by rw [← add_mul, hab, one_mul]

lemma arcDiv_continuous : Continuous (arcDiv : ArcArray V → DivArray V) := by
  unfold arcDiv
  fun_prop

lemma compact_divergences (N : Network V) :
    IsCompact (arcDiv '' {f : ArcArray V | ArcFeasible N f}) :=
  (isCompact_arcFeasible N).image arcDiv_continuous

lemma convex_divergences (N : Network V) :
    Convex ℝ (arcDiv '' {f : ArcArray V | ArcFeasible N f}) :=
  (convex_arcFeasible N).linear_image arcDivLinear

end LeightonRao.Uniform.Proof
-- End ArcTopology

-- Begin PotentialMetric

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]

abbrev Commodity (V : Type) := {st : V × V // st.1 ≠ st.2}

instance commodity_nonempty : Nonempty (Commodity V) := by
  obtain ⟨s,t,hst⟩ := exists_pair_ne V
  exact ⟨⟨(s,t),hst⟩⟩

noncomputable def potentialDist (p : DivArray V) (i j : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun st : Commodity V => |p st.1 i - p st.1 j|)

lemma potentialDist_le_iff (p : DivArray V) (i j : V) (a : ℝ) :
    potentialDist p i j ≤ a ↔ ∀ st : Commodity V, |p st.1 i - p st.1 j| ≤ a := by
  simp [potentialDist, Finset.sup'_le_iff]

lemma abs_potential_le (p : DivArray V) (st : Commodity V) (i j : V) :
    |p st.1 i - p st.1 j| ≤ potentialDist p i j := by
  exact Finset.le_sup' (fun st : Commodity V => |p st.1 i - p st.1 j|) (Finset.mem_univ st)

lemma potentialDist_nonneg (p : DivArray V) (i j : V) : 0 ≤ potentialDist p i j := by
  exact (abs_nonneg _).trans (abs_potential_le p (Classical.choice inferInstance) i j)

lemma potentialDist_symm (p : DivArray V) (i j : V) : potentialDist p i j = potentialDist p j i := by
  simp only [potentialDist, abs_sub_comm]

lemma potentialDist_self (p : DivArray V) (i : V) : potentialDist p i i = 0 := by
  simp [potentialDist]

lemma potentialDist_triangle (p : DivArray V) (i j k : V) :
    potentialDist p i k ≤ potentialDist p i j + potentialDist p j k := by
  rw [potentialDist_le_iff]
  intro st
  exact (abs_sub_le (p st.1 i) (p st.1 j) (p st.1 k)).trans
    (add_le_add (abs_potential_le p st i j) (abs_potential_le p st j k))

noncomputable def potentialMetric (p : DivArray V) : FiniteMetric V where
  d := potentialDist p
  nonneg := potentialDist_nonneg p
  symm := potentialDist_symm p
  self := potentialDist_self p
  triangle := potentialDist_triangle p

lemma potentialDist_attained (p : DivArray V) (i j : V) :
    ∃ st : Commodity V, |p st.1 i - p st.1 j| = potentialDist p i j := by
  obtain ⟨st, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun st : Commodity V => |p st.1 i - p st.1 j|)
  exact ⟨st,h.symm⟩

end LeightonRao.Uniform.Proof
-- End PotentialMetric

-- Begin AtomicFlow

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def singleArc (st ij : V × V) (a : ℝ) : ArcArray V :=
  fun st' ij' => if st' = st then if ij' = ij then a else 0 else 0

omit [Fintype V] in
lemma singleArc_nonneg (st ij : V × V) {a : ℝ} (ha : 0 ≤ a) :
    ∀ st' ij', 0 ≤ singleArc st ij a st' ij' := by
  intros; unfold singleArc; split_ifs <;> positivity

omit [Fintype V] in
lemma singleArc_diag (st ij : V × V) (h : st.1 ≠ st.2) (a : ℝ) (s : V) (uv : V × V) :
    singleArc st ij a (s,s) uv = 0 := by
  have hn : (s,s) ≠ st := by intro he; have := congrArg Prod.fst he; have := congrArg Prod.snd he; grind
  simp [singleArc, hn]

lemma arcLoad_singleArc (st ij : V × V) (a : ℝ) (u v : V) :
    arcLoad (singleArc st ij a) u v =
      (if (u,v) = ij then a else 0) + (if (v,u) = ij then a else 0) := by
  simp [arcLoad, singleArc, Finset.sum_add_distrib]

lemma pair_singleArc (p : DivArray V) (st ij : V × V) (a : ℝ) :
    divPair p (arcDiv (singleArc st ij a)) = a * (p st ij.1 - p st ij.2) := by
  rw [divPair_arcDiv]
  rcases ij with ⟨i,j⟩
  simp [singleArc, Prod.mk.injEq, ite_and]

omit [DecidableEq V] in
lemma arcLoad_sum {I : Type} [Fintype I] (f : I → ArcArray V) (u v : V) :
    arcLoad (∑ i, f i) u v = ∑ i, arcLoad (f i) u v := by
  simp only [arcLoad, Finset.sum_apply]
  simp_rw [← Finset.sum_add_distrib]
  exact Finset.sum_comm

omit [DecidableEq V] in
noncomputable def divPairLinear (p : DivArray V) : DivArray V →ₗ[ℝ] ℝ where
  toFun := divPair p
  map_add' x y := by simp [divPair, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [divPair, mul_left_comm, Finset.mul_sum]

omit [DecidableEq V] in
lemma pair_sum {I : Type} [Fintype I] (p : DivArray V) (f : I → ArcArray V) :
    divPair p (arcDiv (∑ i, f i)) = ∑ i, divPair p (arcDiv (f i)) := by
  exact map_sum ((divPairLinear p).comp arcDivLinear) _ _

lemma exists_oriented_max [Nontrivial V] (p : DivArray V) (ij : V × V) :
    ∃ st : Commodity V, ∃ uv : V × V,
      (uv = ij ∨ uv = ij.swap) ∧ p st.1 uv.1 - p st.1 uv.2 = potentialDist p ij.1 ij.2 := by
  obtain ⟨st,hst⟩ := potentialDist_attained p ij.1 ij.2
  by_cases h : 0 ≤ p st.1 ij.1 - p st.1 ij.2
  · exact ⟨st,ij,Or.inl rfl, by rwa [abs_of_nonneg h] at hst⟩
  · refine ⟨st,ij.swap,Or.inr rfl, ?_⟩
    dsimp
    rw [abs_of_neg (lt_of_not_ge h)] at hst
    linarith

end LeightonRao.Uniform.Proof
-- End AtomicFlow

-- Begin SupportMaximizer

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]

lemma exists_support_maximizer (N : Network V) (p : DivArray V) :
    ∃ f : ArcArray V, ArcFeasible N f ∧
      divPair p (arcDiv f) = metricWeight N (potentialMetric p) := by
  classical
  choose st uv hor hval using (fun ij : V × V => exists_oriented_max p ij)
  let atom : (V × V) → ArcArray V := fun ij => singleArc (st ij).1 (uv ij) (N.C ij.1 ij.2 / 2)
  let f : ArcArray V := ∑ ij, atom ij
  have hload (i j : V) : arcLoad f i j = N.C i j := by
    dsimp [f]
    rw [arcLoad_sum]
    have he (ij : V × V) : arcLoad (atom ij) i j =
        (if (i,j) = ij then N.C ij.1 ij.2 / 2 else 0) +
        (if (j,i) = ij then N.C ij.1 ij.2 / 2 else 0) := by
      dsimp [atom]
      rw [arcLoad_singleArc]
      rcases hor ij with h | h
      · rw [h]
      · rw [h]
        have h1 : (i,j) = ij.swap ↔ (j,i) = ij := by
          cases ij; simp [Prod.mk.injEq, and_comm]
        have h2 : (j,i) = ij.swap ↔ (i,j) = ij := by
          cases ij; simp [Prod.mk.injEq, and_comm]
        rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]
        ring
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [N.C_symm j i]
    ring
  refine ⟨f, ⟨?_, ?_, fun i j => (hload i j).le⟩, ?_⟩
  · intro st' ij'
    dsimp [f]
    simp only [Finset.sum_apply]
    exact Finset.sum_nonneg fun ij _ => singleArc_nonneg _ _ (div_nonneg (N.C_nonneg _ _) (by norm_num)) _ _
  · intro s ij'
    dsimp [f]
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero fun ij _ => singleArc_diag _ _ (st ij).2 _ s ij'
  · dsimp [f]
    rw [pair_sum]
    have he (ij : V × V) : divPair p (arcDiv (atom ij)) =
        (N.C ij.1 ij.2 / 2) * potentialDist p ij.1 ij.2 := by
      rw [show atom ij = singleArc (st ij).1 (uv ij) (N.C ij.1 ij.2 / 2) from rfl,
        pair_singleArc, hval ij]
    simp_rw [he]
    simp only [Fintype.sum_prod_type, metricWeight, potentialMetric]
    simp only [div_eq_mul_inv, one_mul]
    simp_rw [mul_right_comm (N.C _ _) (2 : ℝ)⁻¹]
    simp_rw [← Finset.sum_mul]
    ring


end LeightonRao.Uniform.Proof
-- End SupportMaximizer

-- Begin PotentialPairing

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma sum_potential_delta (p : V → ℝ) (s t : V) (a : ℝ) :
    (∑ v, p v * (a * ((if v = s then 1 else 0) - (if v = t then 1 else 0)))) =
      a * (p s - p t) := by
  simp_rw [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp
  ring

lemma pair_target (p : DivArray V) (lam : ℝ) :
    divPair p (targetDiv lam) = (lam / 2) * ∑ st, (p st st.1 - p st st.2) := by
  unfold divPair targetDiv
  simp_rw [sum_potential_delta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro st _
  by_cases h : st.1 = st.2
  · simp [uniformDemand, h]
  · simp [uniformDemand, h, div_eq_mul_inv]

lemma pair_target_le [Nontrivial V] (p : DivArray V) {lam : ℝ} (hlam : 0 ≤ lam) :
    divPair p (targetDiv lam) ≤ lam * metricMass (potentialMetric p) := by
  rw [pair_target]
  have he : lam * metricMass (potentialMetric p) =
      (lam / 2) * ∑ st : V × V, potentialDist p st.1 st.2 := by
    simp [metricMass, potentialMetric, Fintype.sum_prod_type, div_eq_mul_inv, mul_assoc]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlam (by norm_num))
  apply Finset.sum_le_sum
  intro st _
  by_cases h : st.1 = st.2
  · simp [h, potentialDist_self]
  · exact (le_abs_self _).trans (abs_potential_le p ⟨st,h⟩ st.1 st.2)

lemma functional_eq_pair (L : DivArray V →L[ℝ] ℝ) :
    ∃ p : DivArray V, ∀ q : DivArray V, L q = divPair p q := by
  classical
  let p : DivArray V := fun st v => L (Pi.single st (Pi.single v 1))
  refine ⟨p, fun q => ?_⟩
  have hq : q = ∑ st, ∑ v, q st v • (Pi.single st (Pi.single v 1) : DivArray V) := by
    ext st v
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    simp [ite_apply, Pi.single_apply]
  rw [hq, map_sum]
  simp_rw [map_sum, map_smul]
  change (∑ st, ∑ v, q st v * p st v) = divPair p
    (∑ st, ∑ v, q st v • (Pi.single st (Pi.single v 1) : DivArray V))
  rw [← hq]
  unfold divPair
  apply Finset.sum_congr rfl
  intro st _
  apply Finset.sum_congr rfl
  intro v _
  ring

end LeightonRao.Uniform.Proof
-- End PotentialPairing

-- Begin FlowSeparation

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]

lemma exists_flow_of_metric_bound (N : Network V) {lam : ℝ} (hlam : 0 ≤ lam)
    (hbound : ∀ d : FiniteMetric V, lam * metricMass d ≤ metricWeight N d) :
    ∃ f : V → V → V → V → ℝ, IsConcurrentFlow N uniformDemand f lam := by
  have hb : targetDiv lam ∈ arcDiv '' {f : ArcArray V | ArcFeasible N f} := by
    by_contra hn
    obtain ⟨L,a,hK,ha⟩ := geometric_hahn_banach_closed_point
      (convex_divergences N) (compact_divergences N).isClosed hn
    obtain ⟨p,hp⟩ := functional_eq_pair L
    obtain ⟨f,hf,hfval⟩ := exists_support_maximizer N p
    have hfK := hK (arcDiv f) ⟨f,hf,rfl⟩
    rw [hp, hfval] at hfK
    rw [hp] at ha
    have h1 := pair_target_le p hlam
    have h2 := hbound (potentialMetric p)
    linarith
  obtain ⟨f,hf,he⟩ := hb
  exact ⟨fun s t i j => f (s,t) (i,j), flow_of_arc hf he⟩

end LeightonRao.Uniform.Proof
-- End FlowSeparation

-- Begin SupportBound

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V]

lemma sum_triple_rotate {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma load_metric_pair (f : ArcArray V) (d : FiniteMetric V) :
    (1/2 : ℝ) * (∑ i, ∑ j, arcLoad f i j * d.d i j) =
      ∑ st, ∑ i, ∑ j, f st (i,j) * d.d i j := by
  simp only [arcLoad, Finset.sum_mul]
  rw [sum_triple_rotate]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hs (st : V × V) : (∑ i, ∑ j, f st (j,i) * d.d i j) =
      ∑ i, ∑ j, f st (i,j) * d.d i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [d.symm j i]
  simp_rw [hs]
  ring

lemma pair_arc_le_metricWeight {N : Network V} {f : ArcArray V} (hf : ArcFeasible N f)
    (p : DivArray V) (d : FiniteMetric V)
    (hp : ∀ st : V × V, st.1 ≠ st.2 → ∀ i j, p st i - p st j ≤ d.d i j) :
    divPair p (arcDiv f) ≤ metricWeight N d := by
  rw [divPair_arcDiv]
  calc
    _ ≤ ∑ st, ∑ i, ∑ j, f st (i,j) * d.d i j := by
      apply Finset.sum_le_sum
      intro st _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : st.1 = st.2
      · have hz : f st (i,j) = 0 := by
          have he : st = (st.1,st.1) := by cases st; simp_all
          rw [he]; exact hf.2.1 _ _
        simp [hz]
      · exact mul_le_mul_of_nonneg_left (hp st h i j) (hf.1 st (i,j))
    _ = (1/2 : ℝ) * (∑ i, ∑ j, arcLoad f i j * d.d i j) := (load_metric_pair f d).symm
    _ ≤ metricWeight N d := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hf.2.2 i j) (d.nonneg i j)

end LeightonRao.Uniform.Proof
-- End SupportBound

-- Begin CutExtrema

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev ProperCut (V : Type) [Fintype V] [DecidableEq V] :=
  {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}

lemma properCut_nonempty [Nontrivial V] : Nonempty (ProperCut V) := by
  obtain ⟨s,t,hst⟩ := exists_pair_ne V
  refine ⟨⟨{s}, Finset.singleton_nonempty s, ⟨t, ?_⟩⟩⟩
  simp [Ne.symm hst]

lemma cutCap_nonneg (N : Network V) (U : Finset V) : 0 ≤ cutCap N U := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => N.C_nonneg i j

lemma ratioCost_nonneg (N : Network V) (U : Finset V) : 0 ≤ ratioCost N U :=
  div_nonneg (cutCap_nonneg N U) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma cut_denom_pos (U : ProperCut V) : 0 < (U.1.card : ℝ) * (U.1ᶜ.card : ℝ) := by
  exact mul_pos (by exact_mod_cast U.2.1.card_pos) (by exact_mod_cast U.2.2.card_pos)

lemma minCut_le_ratioCost (N : Network V) (U : ProperCut V) :
    minCut N ≤ ratioCost N U.1 := by
  exact ciInf_le ⟨0, by rintro _ ⟨u,rfl⟩; exact ratioCost_nonneg N u.1⟩ U

lemma minCut_nonneg [Nontrivial V] (N : Network V) : 0 ≤ minCut N := by
  have : Nonempty (ProperCut V) := properCut_nonempty
  exact le_ciInf fun U => ratioCost_nonneg N U.1

lemma minCut_pos [Nontrivial V] (N : Network V) (hN : IsConnectedNet N) : 0 < minCut N := by
  have : Nonempty (ProperCut V) := properCut_nonempty
  obtain ⟨U,hU⟩ := exists_eq_ciInf_of_finite (f := fun U : ProperCut V => ratioCost N U.1)
  change 0 < ⨅ U : ProperCut V, ratioCost N U.1
  rw [← hU]
  exact div_pos (hN U.1 U.2.1 U.2.2) (cut_denom_pos U)

lemma minCut_mul_card_le_cutCap (N : Network V) (U : Finset V)
    (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) :
    minCut N * ((U.card : ℝ) * (Uᶜ.card : ℝ)) ≤ cutCap N U := by
  exact (le_div_iff₀ (cut_denom_pos ⟨U,hU,hUc⟩)).mp (minCut_le_ratioCost N ⟨U,hU,hUc⟩)

end LeightonRao.Uniform.Proof
-- End CutExtrema

-- Begin CutMetric

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def cutMetric (U : Finset V) : FiniteMetric V where
  d i j := if (i ∈ U ↔ j ∈ U) then 0 else 1
  nonneg i j := by split_ifs <;> norm_num
  symm i j := by simp [iff_comm]
  self i := by simp
  triangle i j k := by
    by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;> by_cases hk : k ∈ U <;>
      simp [hi,hj,hk]

lemma sum_ite_mem_const (U : Finset V) (a b : ℝ) :
    (∑ i, if i ∈ U then a else b) = (U.card : ℝ)*a + (Uᶜ.card : ℝ)*b := by
  have hc : Finset.univ.filter (fun x => x ∉ U) = Uᶜ := by ext x; simp
  rw [Finset.sum_ite]
  simp [hc]

lemma cutMetric_mass (U : Finset V) :
    metricMass (cutMetric U) = (U.card : ℝ)*(Uᶜ.card : ℝ) := by
  have he (i : V) : (∑ j, (cutMetric U).d i j) =
      if i ∈ U then (Uᶜ.card : ℝ) else (U.card : ℝ) := by
    by_cases hi : i ∈ U
    · simp only [cutMetric, hi, true_iff, if_true]
      rw [show (∑ j, if j ∈ U then (0:ℝ) else 1) = _ from sum_ite_mem_const U 0 1]
      ring
    · simp only [cutMetric, hi, false_iff, if_false]
      simp_rw [ite_not]
      rw [sum_ite_mem_const]
      ring
  unfold metricMass
  simp_rw [he]
  rw [sum_ite_mem_const]
  ring

lemma cutMetric_weight (N : Network V) (U : Finset V) :
    metricWeight N (cutMetric U) = cutCap N U := by
  have he (i j : V) : N.C i j * (cutMetric U).d i j =
      (if i ∈ U then if j ∈ Uᶜ then N.C i j else 0 else 0) +
      (if i ∈ Uᶜ then if j ∈ U then N.C i j else 0 else 0) := by
    by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;> simp [cutMetric,hi,hj]
  unfold metricWeight
  simp_rw [he, Finset.sum_add_distrib]
  have h1 : (∑ i, ∑ j, if i ∈ U then if j ∈ Uᶜ then N.C i j else 0 else 0) = cutCap N U := by
    simp only [cutCap, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : (∑ i, ∑ j, if i ∈ Uᶜ then if j ∈ U then N.C i j else 0 else 0) = cutCap N U := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
    unfold cutCap
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact N.C_symm j i
  rw [h1,h2]
  ring

end LeightonRao.Uniform.Proof
-- End CutMetric

-- Begin NativeFlow

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma arc_of_flow {N : Network V} {f : V → V → V → V → ℝ} {lam : ℝ}
    (hf : IsConcurrentFlow N uniformDemand f lam) :
    ArcFeasible N (fun st ij => f st.1 st.2 ij.1 ij.2) ∧
      arcDiv (fun st ij => f st.1 st.2 ij.1 ij.2) = targetDiv lam := by
  refine ⟨⟨fun st ij => hf.1 _ _ _ _, fun s ij => hf.2.2.1 _ _ _, ?_⟩, ?_⟩
  · intro i j
    simpa [arcLoad, Fintype.sum_prod_type] using hf.2.2.2 i j
  · ext st v
    by_cases h : st.1 = st.2
    · simp [arcDiv, targetDiv, uniformDemand, h, hf.2.2.1]
    · exact hf.2.1 _ _ h v

lemma zero_concurrentFlow (N : Network V) :
    IsConcurrentFlow N uniformDemand (fun _ _ _ _ => 0) 0 := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro i j
  simpa using N.C_nonneg i j

end LeightonRao.Uniform.Proof
-- End NativeFlow

-- Begin WeakDuality

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def cutPotential (U : Finset V) : DivArray V :=
  fun st v => if st.1 ∈ U then (if v ∈ U then 1 else 0) else -(if v ∈ U then 1 else 0)

omit [Fintype V] in
lemma cutPotential_bound (U : Finset V) (st : V × V) (i j : V) :
    cutPotential U st i - cutPotential U st j ≤ (cutMetric U).d i j := by
  by_cases hs : st.1 ∈ U <;> by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;>
    norm_num [cutPotential,cutMetric,hs,hi,hj]

lemma pair_cut_target (U : Finset V) (lam : ℝ) :
    divPair (cutPotential U) (targetDiv lam) = lam * metricMass (cutMetric U) := by
  rw [pair_target]
  have he (st : V × V) : cutPotential U st st.1 - cutPotential U st st.2 =
      (cutMetric U).d st.1 st.2 := by
    by_cases hs : st.1 ∈ U <;> by_cases ht : st.2 ∈ U <;>
      norm_num [cutPotential,cutMetric,hs,ht]
  simp_rw [he]
  simp only [metricMass, Fintype.sum_prod_type]
  ring

lemma flow_cut_bound {N : Network V} {f : V → V → V → V → ℝ} {lam : ℝ}
    (hf : IsConcurrentFlow N uniformDemand f lam) (U : Finset V) :
    lam * ((U.card : ℝ) * (Uᶜ.card : ℝ)) ≤ cutCap N U := by
  obtain ⟨ha,hd⟩ := arc_of_flow hf
  have hb := pair_arc_le_metricWeight ha (cutPotential U) (cutMetric U)
    (fun st _ i j => cutPotential_bound U st i j)
  rwa [hd, pair_cut_target, cutMetric_mass, cutMetric_weight] at hb

end LeightonRao.Uniform.Proof
-- End WeakDuality

-- Begin FlowExtrema

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]

lemma flow_le_minCut {N : Network V} {f : V → V → V → V → ℝ} {lam : ℝ}
    (hf : IsConcurrentFlow N uniformDemand f lam) : lam ≤ minCut N := by
  have : Nonempty (ProperCut V) := properCut_nonempty
  apply le_ciInf
  intro U
  exact (le_div_iff₀ (cut_denom_pos U)).mpr (flow_cut_bound hf U.1)

lemma flow_values_bddAbove (N : Network V) :
    BddAbove {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N uniformDemand f lam} := by
  refine ⟨minCut N, ?_⟩
  rintro lam ⟨_,f,hf⟩
  exact flow_le_minCut hf

omit [Nontrivial V] in
lemma flow_values_nonempty (N : Network V) :
    Set.Nonempty {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N uniformDemand f lam} :=
  ⟨0, le_rfl, _, zero_concurrentFlow N⟩

lemma maxFlow_le_minCut (N : Network V) : maxFlow N uniformDemand ≤ minCut N := by
  apply csSup_le (flow_values_nonempty N)
  rintro lam ⟨_,f,hf⟩
  exact flow_le_minCut hf

lemma le_maxFlow_of_feasible {N : Network V} {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : ∃ f, IsConcurrentFlow N uniformDemand f lam) : lam ≤ maxFlow N uniformDemand :=
  le_csSup (flow_values_bddAbove N) ⟨hlam,hf⟩

lemma maxFlow_nonneg (N : Network V) : 0 ≤ maxFlow N uniformDemand :=
  le_maxFlow_of_feasible le_rfl ⟨_, zero_concurrentFlow N⟩

end LeightonRao.Uniform.Proof
-- End FlowExtrema

-- Begin MetricFiniteSums

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def restrictedWeight (N : Network V) (d : FiniteMetric V) (R : Finset V) : ℝ :=
  (1/2) * ∑ u, ∑ v, if u ∈ R ∧ v ∈ R then N.C u v * d.d u v else 0

noncomputable def crossWeight {L : Type*} [DecidableEq L] (N : Network V)
    (R : Finset V) (label : V → L) : ℝ :=
  (1/2) * ∑ u, ∑ v, if u ∈ R ∧ v ∈ R ∧ label u ≠ label v then N.C u v else 0

noncomputable def ballSet (d : FiniteMetric V) (R : Finset V) (c : V) (r : ℝ) : Finset V :=
  R.filter (fun u => d.d c u < r)

omit [DecidableEq V] in
lemma metricWeight_nonneg (N : Network V) (d : FiniteMetric V) : 0 ≤ metricWeight N d := by
  unfold metricWeight
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
    mul_nonneg (N.C_nonneg u v) (d.nonneg u v)

lemma restrictedWeight_nonneg (N : Network V) (d : FiniteMetric V) (R : Finset V) :
    0 ≤ restrictedWeight N d R := by
  unfold restrictedWeight
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
    split_ifs
    · exact mul_nonneg (N.C_nonneg u v) (d.nonneg u v)
    · exact le_refl 0

lemma restrictedWeight_le (N : Network V) (d : FiniteMetric V) (R : Finset V) :
    restrictedWeight N d R ≤ metricWeight N d := by
  unfold restrictedWeight metricWeight
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
    split_ifs
    · exact le_refl _
    · exact mul_nonneg (N.C_nonneg u v) (d.nonneg u v)

lemma restrictedWeight_univ (N : Network V) (d : FiniteMetric V) :
    restrictedWeight N d Finset.univ = metricWeight N d := by
  simp [restrictedWeight,metricWeight]

lemma restrictedWeight_empty (N : Network V) (d : FiniteMetric V) :
    restrictedWeight N d ∅ = 0 := by simp [restrictedWeight]

lemma crossWeight_nonneg {L : Type*} [DecidableEq L] (N : Network V)
    (R : Finset V) (label : V → L) : 0 ≤ crossWeight N R label := by
  unfold crossWeight
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
    split_ifs
    · exact N.C_nonneg u v
    · exact le_refl 0

omit [Fintype V] [DecidableEq V] in
lemma ballSet_subset (d : FiniteMetric V) (R : Finset V) (c : V) (r : ℝ) :
    ballSet d R c r ⊆ R := Finset.filter_subset _ _

omit [Fintype V] [DecidableEq V] in
lemma center_mem_ballSet (d : FiniteMetric V) (R : Finset V) {c : V} {r : ℝ}
    (hc : c ∈ R) (hr : 0 < r) : c ∈ ballSet d R c r := by
  simp [ballSet,hc,d.self,hr]

omit [Fintype V] [DecidableEq V] in
lemma ballSet_diameter (d : FiniteMetric V) (R : Finset V) (c : V) (r : ℝ)
    {u v : V} (hu : u ∈ ballSet d R c r) (hv : v ∈ ballSet d R c r) :
    d.d u v < 2*r := by
  have hu' := (Finset.mem_filter.mp hu).2
  have hv' := (Finset.mem_filter.mp hv).2
  have ht := d.triangle u c v
  rw [d.symm u c] at ht
  linarith

omit [Fintype V] [DecidableEq V] in
lemma metric_reverse_triangle (d : FiniteMetric V) (c u v : V) :
    |d.d c u - d.d c v| ≤ d.d u v := by
  rw [abs_le]
  constructor
  · have h := d.triangle c u v
    linarith
  · have h := d.triangle c v u
    rw [d.symm v u] at h
    linarith

lemma crossWeight_split (N : Network V) (R B : Finset V) (label : V → ℕ) :
    crossWeight N R (fun u => if u ∈ B then 0 else label u + 1) =
      crossWeight N R (fun u => decide (u ∈ B)) + crossWeight N (R \ B) label := by
  unfold crossWeight
  rw [← mul_add,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hur : u ∈ R <;> by_cases hvr : v ∈ R <;>
    by_cases hub : u ∈ B <;> by_cases hvb : v ∈ B <;>
    simp [hur,hvr,hub,hvb]

end LeightonRao.Uniform.Proof
-- End MetricFiniteSums

-- Begin ClippedRamp

open Filter Set
open scoped Topology
namespace LeightonRao.Uniform.Proof

def clippedRamp (a b r : ℝ) : ℝ := min (max (r-a) 0) (b-a)

lemma clippedRamp_nonneg {a b r : ℝ} (h : a ≤ b) : 0 ≤ clippedRamp a b r :=
  le_min (le_max_right _ _) (sub_nonneg.mpr h)

lemma clippedRamp_le {a b r : ℝ} : clippedRamp a b r ≤ b-a := min_le_right _ _

lemma clippedRamp_zero {a b r : ℝ} (hab : a ≤ b) (hr : r ≤ a) :
    clippedRamp a b r = 0 := by
  simp [clippedRamp, max_eq_right (sub_nonpos.mpr hr), min_eq_left (sub_nonneg.mpr hab)]

lemma clippedRamp_continuous (a b : ℝ) : Continuous (clippedRamp a b) := by
  exact ((continuous_id.sub continuous_const).max continuous_const).min continuous_const

lemma clippedRamp_hasDerivAt {a b r : ℝ} (hab : a ≤ b) (hra : r ≠ a) (hrb : r ≠ b) :
    HasDerivAt (clippedRamp a b) (if a < r ∧ r < b then 1 else 0) r := by
  rcases lt_or_gt_of_ne hra with hr | hr
  · have heq : clippedRamp a b =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      exact clippedRamp_zero hab hx.le
    simpa [not_lt.mpr hr.le] using (hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq heq
  · rcases lt_or_gt_of_ne hrb with hb | hb
    · have heq : clippedRamp a b =ᶠ[𝓝 r] fun x => x-a := by
        filter_upwards [Ioi_mem_nhds hr, Iio_mem_nhds hb] with x hxa hxb
        change a < x at hxa
        change x < b at hxb
        simp [clippedRamp, max_eq_left (sub_nonneg.mpr hxa.le),
          min_eq_left (sub_le_sub_right hxb.le a)]
      simpa [hr,hb] using ((hasDerivAt_id r).sub_const a).congr_of_eventuallyEq heq
    · have heq : clippedRamp a b =ᶠ[𝓝 r] fun _ => b-a := by
        filter_upwards [Ioi_mem_nhds hb] with x hx
        change b < x at hx
        rw [clippedRamp, max_eq_left (by linarith), min_eq_right (by linarith)]
      simpa [not_lt.mpr hb.le] using (hasDerivAt_const r (b-a)).congr_of_eventuallyEq heq

end LeightonRao.Uniform.Proof
-- End ClippedRamp

-- Begin BallVolume

open Set
open scoped BigOperators Topology
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def ballVolume (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base r : ℝ) : ℝ :=
  base + (1/2) * ∑ u, ∑ v, if u ∈ R ∧ v ∈ R then
    N.C u v * clippedRamp (min (d.d c u) (d.d c v)) (max (d.d c u) (d.d c v)) r else 0

lemma ballVolume_continuous (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base : ℝ) : Continuous (ballVolume N d R c base) := by
  unfold ballVolume
  apply continuous_const.add
  apply continuous_const.mul
  apply continuous_finsetSum
  intro u hu
  apply continuous_finsetSum
  intro v hv
  split_ifs
  · exact continuous_const.mul (clippedRamp_continuous _ _)
  · exact continuous_const

lemma ballVolume_ge (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base r : ℝ) : base ≤ ballVolume N d R c base r := by
  unfold ballVolume
  apply le_add_of_nonneg_right
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
    split_ifs
    · exact mul_nonneg (N.C_nonneg _ _) (clippedRamp_nonneg (min_le_max))
    · exact le_refl 0

lemma ballVolume_zero (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base : ℝ) : ballVolume N d R c base 0 = base := by
  have hz : ∀ u v, clippedRamp (min (d.d c u) (d.d c v))
      (max (d.d c u) (d.d c v)) 0 = 0 := fun u v =>
    clippedRamp_zero min_le_max (le_min (d.nonneg c u) (d.nonneg c v))
  simp [ballVolume,hz]

lemma ballVolume_upper (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base r : ℝ) :
    ballVolume N d R c base r ≤ base + restrictedWeight N d R := by
  unfold ballVolume restrictedWeight
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
    split_ifs
    · apply mul_le_mul_of_nonneg_left _ (N.C_nonneg u v)
      calc
        clippedRamp _ _ r ≤ max (d.d c u) (d.d c v) - min (d.d c u) (d.d c v) := clippedRamp_le
        _ = |d.d c u - d.d c v| := (max_sub_min_eq_abs _ _).trans (abs_sub_comm _ _)
        _ ≤ d.d u v := metric_reverse_triangle d c u v
    · exact le_refl _

lemma ballVolume_budget (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base r : ℝ) :
    ballVolume N d R c base r + restrictedWeight N d (R \ ballSet d R c r) ≤
      base + restrictedWeight N d R := by
  unfold ballVolume restrictedWeight
  rw [add_assoc,← mul_add,← Finset.sum_add_distrib]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro u hu
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  by_cases hur : u ∈ R <;> by_cases hvr : v ∈ R
  · by_cases hub : u ∈ ballSet d R c r <;> by_cases hvb : v ∈ ballSet d R c r
    · simp only [hur,hvr,hub,hvb,Finset.mem_sdiff,and_self,not_true_eq_false,and_false,if_true,if_false,add_zero]
      exact mul_le_mul_of_nonneg_left (clippedRamp_le.trans
        (((max_sub_min_eq_abs _ _).trans (abs_sub_comm _ _)).trans_le (metric_reverse_triangle d c u v))) (N.C_nonneg u v)
    · simp only [hur,hvr,hub,hvb,Finset.mem_sdiff,and_self,not_true_eq_false,and_false,false_and,if_true,if_false,add_zero]
      exact mul_le_mul_of_nonneg_left (clippedRamp_le.trans
        (((max_sub_min_eq_abs _ _).trans (abs_sub_comm _ _)).trans_le (metric_reverse_triangle d c u v))) (N.C_nonneg u v)
    · simp only [hur,hvr,hub,hvb,Finset.mem_sdiff,and_self,not_true_eq_false,and_false,if_true,if_false,add_zero]
      exact mul_le_mul_of_nonneg_left (clippedRamp_le.trans
        (((max_sub_min_eq_abs _ _).trans (abs_sub_comm _ _)).trans_le (metric_reverse_triangle d c u v))) (N.C_nonneg u v)
    · have hu' : r ≤ d.d c u := by simpa [ballSet,hur] using hub
      have hv' : r ≤ d.d c v := by simpa [ballSet,hvr] using hvb
      rw [clippedRamp_zero min_le_max (le_min hu' hv')]
      simp [hur,hvr,hub,hvb]
  · simp [hur,hvr,Finset.mem_sdiff]
  · simp [hur,hvr,Finset.mem_sdiff]
  · simp [hur,hvr,Finset.mem_sdiff]

end LeightonRao.Uniform.Proof
-- End BallVolume

-- Begin FiniteMeanValue

open Set
namespace LeightonRao.Uniform.Proof

lemma strict_inc_off_finset (s : Finset ℝ) {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (g x) x)
    (hp : ∀ x ∈ Ioo a b, x ∉ s → 0 < g x) : f a < f b := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
    have hm := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
      (fun x hx => by
        rw [(hd x (by simpa using hx) (by simp)).deriv]
        exact hp x (by simpa using hx) (by simp))
    exact hm (by simp [hab.le]) (by simp [hab.le]) hab
  | @insert c s hcs ih =>
    by_cases hcin : c ∈ Ioo a b
    · have hleft : f a < f c := ih hcin.1 (hc.mono (Icc_subset_Icc_right hcin.2.le))
        (fun x hx hxs => hd x ⟨hx.1,hx.2.trans hcin.2⟩ (by simp [hxs, ne_of_lt hx.2]))
        (fun x hx hxs => hp x ⟨hx.1,hx.2.trans hcin.2⟩ (by simp [hxs, ne_of_lt hx.2]))
      have hright : f c < f b := ih hcin.2 (hc.mono (Icc_subset_Icc_left hcin.1.le))
        (fun x hx hxs => hd x ⟨hcin.1.trans hx.1,hx.2⟩ (by simp [hxs, ne_of_gt hx.1]))
        (fun x hx hxs => hp x ⟨hcin.1.trans hx.1,hx.2⟩ (by simp [hxs, ne_of_gt hx.1]))
      exact hleft.trans hright
    · apply ih hab hc
      · intro x hx hxs
        apply hd x hx
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hcin (h ▸ hx),hxs⟩
      · intro x hx hxs
        apply hp x hx
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hcin (h ▸ hx),hxs⟩

lemma inc_off_finset (s : Finset ℝ) {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (g x) x)
    (hp : ∀ x ∈ Ioo a b, x ∉ s → 0 ≤ g x) : f a ≤ f b := by
  by_contra hn
  have hlt : f b < f a := lt_of_not_ge hn
  let e := (f a-f b)/(2*(b-a))
  have he : 0 < e := div_pos (sub_pos.mpr hlt) (by linarith)
  have hh := strict_inc_off_finset s (f := fun x => f x+e*x) (g := fun x => g x+e)
    hab (hc.add (continuous_const.mul continuous_id).continuousOn)
    (fun x hx hs => (hd x hx hs).add (by simpa using (hasDerivAt_id x).const_mul e))
    (fun x hx hs => add_pos_of_nonneg_of_pos (hp x hx hs) he)
  have heq : e*(2*(b-a))=f a-f b := div_mul_cancel₀ _ (by linarith)
  nlinarith

lemma exists_deriv_le_off_finset (s : Finset ℝ) {f g : ℝ → ℝ} {a b K : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (g x) x)
    (hbound : f b - f a ≤ K * (b-a)) :
    ∃ x ∈ Ioo a b, x ∉ s ∧ g x ≤ K := by
  classical
  by_contra hn
  push Not at hn
  have hh := strict_inc_off_finset s (f := fun x => f x-K*x) (g := fun x => g x-K)
    hab (hc.sub (continuous_const.mul continuous_id).continuousOn)
    (fun x hx hs => (hd x hx hs).sub (by simpa using (hasDerivAt_id x).const_mul K))
    (fun x hx hs => sub_pos.mpr (hn x hx hs))
  linarith

end LeightonRao.Uniform.Proof
-- End FiniteMeanValue

-- Begin BallDerivative

open Set
open scoped BigOperators
namespace LeightonRao.Uniform.Proof

lemma minmax_cross_indicator {a b r : ℝ} (ha : r ≠ a) (hb : r ≠ b) :
    (if min a b < r ∧ r < max a b then (1:ℝ) else 0) =
      if decide (a < r) ≠ decide (b < r) then 1 else 0 := by
  by_cases har : a < r <;> by_cases hbr : b < r
  · simp [har,hbr,not_lt.mpr har.le,not_lt.mpr hbr.le]
  · have hrb : r < b := lt_of_le_of_ne (le_of_not_gt hbr) hb
    simp [har,hbr,hrb]
  · have hra : r < a := lt_of_le_of_ne (le_of_not_gt har) ha
    simp [har,hbr,hra]
  · have hra : r < a := lt_of_le_of_ne (le_of_not_gt har) ha
    have hrb : r < b := lt_of_le_of_ne (le_of_not_gt hbr) hb
    simp [har,hbr]

variable {V : Type} [Fintype V] [DecidableEq V]

lemma ballVolume_hasDerivAt (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) (base r : ℝ) (hr : ∀ u, r ≠ d.d c u) :
    HasDerivAt (ballVolume N d R c base)
      (crossWeight N R (fun u => decide (u ∈ ballSet d R c r))) r := by
  classical
  have hterm : ∀ u v, HasDerivAt
      (fun x => if u ∈ R ∧ v ∈ R then N.C u v *
        clippedRamp (min (d.d c u) (d.d c v)) (max (d.d c u) (d.d c v)) x else 0)
      (if u ∈ R ∧ v ∈ R ∧ decide (u ∈ ballSet d R c r) ≠
        decide (v ∈ ballSet d R c r) then N.C u v else 0) r := by
    intro u v
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R
    · have hmin : r ≠ min (d.d c u) (d.d c v) := by
        rw [ne_eq,min_def]; split_ifs <;> exact hr _
      have hmax : r ≠ max (d.d c u) (d.d c v) := by
        rw [ne_eq,max_def]; split_ifs <;> exact hr _
      have h := (clippedRamp_hasDerivAt min_le_max hmin hmax).const_mul (N.C u v)
      rw [minmax_cross_indicator (hr u) (hr v)] at h
      simpa [ballSet,hu,hv,mul_ite] using h
    · simp only [hu,hv,and_false,if_false,false_and]
      exact hasDerivAt_const _ _
    · simp only [hu,hv,false_and,if_false]
      exact hasDerivAt_const _ _
    · simp only [hu,hv,false_and,if_false]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (fun u (_ : u ∈ Finset.univ) =>
    HasDerivAt.fun_sum (fun v (_ : v ∈ Finset.univ) => hterm u v))
  exact (hsum.const_mul (1/2:ℝ)).const_add base

lemma small_boundary_ball (N : Network V) (d : FiniteMetric V) (R : Finset V)
    (c : V) {base W Δ : ℝ} (hbase : 0 < base) (hW : 0 ≤ W) (hΔ : 0 < Δ)
    (hweight : restrictedWeight N d R ≤ W) :
    ∃ r, 0 < r ∧ r < Δ ∧
      crossWeight N R (fun u => decide (u ∈ ballSet d R c r)) ≤
        (Real.log (1+W/base)/Δ) * ballVolume N d R c base r := by
  classical
  let f := ballVolume N d R c base
  let boundary := fun r => crossWeight N R (fun u => decide (u ∈ ballSet d R c r))
  have hfpos : ∀ r, 0 < f r := fun r => hbase.trans_le (ballVolume_ge N d R c base r)
  have hc : Continuous (fun r => Real.log (f r)) :=
    (ballVolume_continuous N d R c base).log (fun r => (hfpos r).ne')
  have hd : ∀ r ∈ Ioo 0 Δ, r ∉ Finset.univ.image (d.d c) →
      HasDerivAt (fun r => Real.log (f r)) (boundary r / f r) r := by
    intro r _ hr
    have hne : ∀ u, r ≠ d.d c u := by
      intro u he
      apply hr
      exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,he.symm⟩
    exact (ballVolume_hasDerivAt N d R c base r hne).log (hfpos r).ne'
  have hbound : Real.log (f Δ) - Real.log (f 0) ≤
      (Real.log (1+W/base)/Δ)*(Δ-0) := by
    have hfupper : f Δ ≤ base+W := (ballVolume_upper N d R c base Δ).trans (add_le_add le_rfl hweight)
    have hl := Real.log_le_log (hfpos Δ) hfupper
    have hbW : 0 < base+W := by positivity
    rw [show f 0 = base from ballVolume_zero N d R c base]
    rw [sub_zero,div_mul_cancel₀ _ hΔ.ne']
    calc
      Real.log (f Δ)-Real.log base ≤ Real.log (base+W)-Real.log base := sub_le_sub_right hl _
      _ = Real.log (1+W/base) := by
        rw [← Real.log_div hbW.ne' hbase.ne']
        congr 1
        field_simp

  obtain ⟨r,hr,_,hle⟩ := exists_deriv_le_off_finset (Finset.univ.image (d.d c))
    hΔ hc.continuousOn hd hbound
  exact ⟨r,hr.1,hr.2,(div_le_iff₀ (hfpos r)).mp hle⟩

end LeightonRao.Uniform.Proof
-- End BallDerivative

-- Begin MetricPartition

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma metric_partition (N : Network V) (d : FiniteMetric V) {base Δ : ℝ}
    (hbase : 0 < base) (hΔ : 0 < Δ) (R : Finset V) :
    ∃ label : V → ℕ,
      (∀ u ∈ R, ∀ v ∈ R, label u = label v → d.d u v ≤ 2*Δ) ∧
      crossWeight N R label ≤ (Real.log (1+metricWeight N d/base)/Δ) *
        ((R.card:ℝ)*base + restrictedWeight N d R) := by
  classical
  let K := Real.log (1+metricWeight N d/base)/Δ
  have hK : 0 ≤ K := div_nonneg
    (Real.log_nonneg (by linarith [div_nonneg (metricWeight_nonneg N d) hbase.le])) hΔ.le
  refine Finset.strongInductionOn R ?_
  intro R ih
  by_cases hR : R.Nonempty
  · obtain ⟨c,hc⟩ := hR
    obtain ⟨r,hr,hrΔ,hcut⟩ := small_boundary_ball N d R c hbase
      (metricWeight_nonneg N d) hΔ (restrictedWeight_le N d R)
    let B := ballSet d R c r
    let D := R \ B
    have hcB : c ∈ B := center_mem_ballSet d R hc hr
    have hDR : D ⊆ R := Finset.sdiff_subset
    have hlt : D.card < R.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hDR,fun he => by have : c ∈ D := he.symm ▸ hc; simp [D,hcB] at this⟩)
    obtain ⟨label,hdiam,hcross⟩ := ih D (Finset.ssubset_iff_subset_ne.mpr
      ⟨hDR,fun he => by have : c ∈ D := he.symm ▸ hc; simp [D,hcB] at this⟩)
    refine ⟨fun u => if u ∈ B then 0 else label u+1,?_,?_⟩
    · intro u hu v hv he
      by_cases hub : u ∈ B <;> by_cases hvb : v ∈ B
      · exact (ballSet_diameter d R c r hub hvb).le.trans (by linarith)
      · simp [hub,hvb] at he
      · simp [hub,hvb] at he
      · apply hdiam u (Finset.mem_sdiff.mpr ⟨hu,hub⟩) v (Finset.mem_sdiff.mpr ⟨hv,hvb⟩)
        simpa [hub,hvb] using he
    · rw [crossWeight_split]
      have hbudget := ballVolume_budget N d R c base r
      have hcard : (D.card:ℝ)+1 ≤ R.card := by exact_mod_cast Nat.succ_le_of_lt hlt
      change crossWeight N R (fun u => decide (u ∈ B)) + crossWeight N D label ≤
        K*((R.card:ℝ)*base+restrictedWeight N d R)
      change crossWeight N R (fun u => decide (u ∈ B)) ≤ K*ballVolume N d R c base r at hcut
      change crossWeight N D label ≤ K*((D.card:ℝ)*base+restrictedWeight N d D) at hcross
      change ballVolume N d R c base r+restrictedWeight N d D ≤ base+restrictedWeight N d R at hbudget
      nlinarith [mul_nonneg hK (sub_nonneg.mpr hbudget),
        mul_nonneg hK (mul_nonneg (sub_nonneg.mpr hcard) hbase.le)]
  · refine ⟨fun _ => 0,?_,?_⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hR]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hR,crossWeight,restrictedWeight]

end LeightonRao.Uniform.Proof
-- End MetricPartition

-- Begin MetricWeightPositive

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma metricMass_nonneg (d : FiniteMetric V) : 0 ≤ metricMass d := by
  unfold metricMass
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => d.nonneg u v

lemma metricWeight_pos (N : Network V) (hN : IsConnectedNet N) (d : FiniteMetric V)
    (hA : 0 < metricMass d) : 0 < metricWeight N d := by
  classical
  by_contra hn
  have hW : metricWeight N d = 0 := le_antisymm (le_of_not_gt hn) (metricWeight_nonneg N d)
  have hsum : ∑ u, ∑ v, N.C u v*d.d u v = 0 := by
    unfold metricWeight at hW
    linarith
  have hp : ∀ u v, N.C u v*d.d u v = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun u (_ : u ∈ Finset.univ) =>
      Finset.sum_nonneg (fun v _ => mul_nonneg (N.C_nonneg u v) (d.nonneg u v)))).mp hsum
    intro u v
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ Finset.univ) =>
      mul_nonneg (N.C_nonneg u v) (d.nonneg u v))).mp (hh u (Finset.mem_univ _)) v (Finset.mem_univ _)
  have hz : ∀ c v, d.d c v = 0 := by
    intro c v
    by_contra hcv
    let U := Finset.univ.filter (fun u => d.d c u = 0)
    have hcU : c ∈ U := by simp [U,d.self]
    have hvU : v ∈ Uᶜ := by simp [U,hcv]
    have hpositive := hN U ⟨c,hcU⟩ ⟨v,hvU⟩
    have hzero : cutCap N U = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro w hw
      have hcu : d.d c u = 0 := by simpa [U] using hu
      have hcw : d.d c w ≠ 0 := by simpa [U] using hw
      have hdist : 0 < d.d u w := by
        have ht := d.triangle c u w
        have hpos := lt_of_le_of_ne (d.nonneg c w) (Ne.symm hcw)
        linarith
      exact (mul_eq_zero.mp (hp u w)).resolve_right hdist.ne'
    linarith
  have : metricMass d = 0 := by simp [metricMass,hz]
  linarith

end LeightonRao.Uniform.Proof
-- End MetricWeightPositive

-- Begin BalancedFibers

namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

def FiberClosed (label : V → ℕ) (U : Finset V) : Prop :=
  ∀ u v, label u = label v → (u ∈ U ↔ v ∈ U)

noncomputable def labelFiber (label : V → ℕ) (v : V) : Finset V :=
  Finset.univ.filter (fun u => label u = label v)

omit [Fintype V] [DecidableEq V] in
lemma fiberClosed_empty (label : V → ℕ) : FiberClosed label ∅ := by simp [FiberClosed]

omit [DecidableEq V] in
lemma labelFiber_closed (label : V → ℕ) (v : V) : FiberClosed label (labelFiber label v) := by
  intro u w he
  simp [labelFiber,he]

omit [Fintype V] in
lemma FiberClosed.union {label : V → ℕ} {U B : Finset V}
    (hU : FiberClosed label U) (hB : FiberClosed label B) : FiberClosed label (U ∪ B) := by
  intro u v he
  simp only [Finset.mem_union,hU u v he,hB u v he]

lemma balanced_fiber_union (label : V → ℕ) (hn : 0 < Fintype.card V)
    (hsmall : ∀ v, ((labelFiber label v).card:ℝ) < 2*(Fintype.card V:ℝ)/3) :
    ∃ U : Finset V, FiberClosed label U ∧
      (Fintype.card V:ℝ)/3 ≤ U.card ∧ (U.card:ℝ) ≤ 2*(Fintype.card V:ℝ)/3 := by
  classical
  by_cases hmid : ∃ v, (Fintype.card V:ℝ)/3 ≤ (labelFiber label v).card
  · obtain ⟨v,hv⟩ := hmid
    exact ⟨labelFiber label v,labelFiber_closed label v,hv,(hsmall v).le⟩
  push Not at hmid
  let S : Finset (Finset V) := Finset.univ.filter
    (fun U => FiberClosed label U ∧ (U.card:ℝ)<(Fintype.card V:ℝ)/3)
  have hSn : S.Nonempty := ⟨∅,by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_empty,Nat.cast_zero]
    exact ⟨fiberClosed_empty label,by positivity⟩⟩
  obtain ⟨U,hUS,hmax⟩ := Finset.exists_max_image S Finset.card hSn
  have hU := (Finset.mem_filter.mp hUS).2
  have hproper : U ≠ Finset.univ := by
    intro he
    rw [he,Finset.card_univ] at hU
    have : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
    linarith [hU.2]
  have hvex : ∃ v, v ∉ U := by
    by_contra hh
    push Not at hh
    exact hproper (Finset.eq_univ_of_forall hh)
  obtain ⟨v,hv⟩ := hvex
  let B := labelFiber label v
  have hvB : v ∈ B := by simp [B,labelFiber]
  have hdis : Disjoint U B := by
    apply Finset.disjoint_left.mpr
    intro u hu hub
    have he : label u = label v := by simpa [B,labelFiber] using hub
    exact hv ((hU.1 u v he).mp hu)
  have hclosed := hU.1.union (labelFiber_closed label v)
  have hcard : (U ∪ B).card = U.card+B.card := Finset.card_union_of_disjoint hdis
  have hlow : (Fintype.card V:ℝ)/3 ≤ (U ∪ B).card := by
    by_contra hh
    have hmem : U ∪ B ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hclosed,lt_of_not_ge hh⟩
    have hm := hmax (U ∪ B) hmem
    have hbpos : 0 < B.card := Finset.card_pos.mpr ⟨v,hvB⟩
    omega
  refine ⟨U ∪ B,hclosed,hlow,?_⟩
  rw [hcard,Nat.cast_add]
  have hb := hmid v
  change (B.card:ℝ)<(Fintype.card V:ℝ)/3 at hb
  linarith [hU.2]

end LeightonRao.Uniform.Proof
-- End BalancedFibers

-- Begin CutCross

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cutCap_eq_sum (N : Network V) (U : Finset V) :
    cutCap N U = ∑ u, ∑ v, if u ∈ U ∧ v ∉ U then N.C u v else 0 := by
  classical
  simp only [cutCap,Finset.sum_ite_irrel,ite_and]
  simp
  apply Finset.sum_congr rfl
  intro u hu
  rw [show Uᶜ = Finset.univ.filter (fun v => v ∉ U) from by ext; simp]
  simp [Finset.sum_filter]

lemma crossWeight_cut (N : Network V) (U : Finset V) :
    crossWeight N Finset.univ (fun u => decide (u ∈ U)) = cutCap N U := by
  classical
  have hs : (∑ u, ∑ v, if u ∉ U ∧ v ∈ U then N.C u v else 0) = cutCap N U := by
    rw [cutCap_eq_sum,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [N.C_symm u v]
    simp [and_comm]
  have hp : ∀ u v, (if decide (u ∈ U) ≠ decide (v ∈ U) then N.C u v else 0) =
      (if u ∈ U ∧ v ∉ U then N.C u v else 0) +
      (if u ∉ U ∧ v ∈ U then N.C u v else 0) := by
    intro u v
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;> simp [hu,hv]
  simp only [crossWeight,Finset.mem_univ,true_and,hp,Finset.sum_add_distrib]
  rw [← cutCap_eq_sum,hs]
  ring

lemma cutCap_le_crossWeight (N : Network V) (label : V → ℕ) (U : Finset V)
    (hU : FiberClosed label U) : cutCap N U ≤ crossWeight N Finset.univ label := by
  rw [← crossWeight_cut]
  unfold crossWeight
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  simp only [Finset.mem_univ,true_and]
  by_cases he : label u = label v
  · have hm := hU u v he
    simp [he,hm]
  · split_ifs
    · exact le_refl _
    · exact N.C_nonneg u v

end LeightonRao.Uniform.Proof
-- End CutCross

-- Begin NormalizedPartition

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma normalized_partition (N : Network V) (hN : IsConnectedNet N) (d : FiniteMetric V)
    (hn : 2 ≤ Fintype.card V) (hA : 0 < metricMass d) :
    ∃ label : V → ℕ,
      (∀ u v, label u = label v → d.d u v ≤ metricMass d/(2*(Fintype.card V:ℝ)^2)) ∧
      crossWeight N Finset.univ label ≤
        8*(Fintype.card V:ℝ)^2*metricWeight N d*Real.log ((Fintype.card V:ℝ)+1)/metricMass d := by
  have hnpos : (0:ℝ)<Fintype.card V := by exact_mod_cast (by omega : 0<Fintype.card V)
  have hW := metricWeight_pos N hN d hA
  let base := metricWeight N d/(Fintype.card V:ℝ)
  let Δ := metricMass d/(4*(Fintype.card V:ℝ)^2)
  have hbase : 0 < base := div_pos hW hnpos
  have hΔ : 0 < Δ := div_pos hA (by positivity)
  obtain ⟨label,hdiam,hcross⟩ := metric_partition N d hbase hΔ Finset.univ
  refine ⟨label,?_,?_⟩
  · intro u v he
    have hh := hdiam u (Finset.mem_univ _) v (Finset.mem_univ _) he
    convert hh using 1; dsimp [Δ]; ring
  · rw [Finset.card_univ,restrictedWeight_univ] at hcross
    convert hcross using 1
    dsimp [base,Δ]
    have hlog : 1+metricWeight N d/(metricWeight N d/(Fintype.card V:ℝ)) =
        (Fintype.card V:ℝ)+1 := by field_simp; ring
    rw [hlog]
    field_simp
    ring

lemma partition_cut_or_large (N : Network V) (hN : IsConnectedNet N) (d : FiniteMetric V)
    (hn : 2 ≤ Fintype.card V) (hA : 0 < metricMass d) :
    (∃ T : Finset V, T.Nonempty ∧ 2*(Fintype.card V:ℝ)/3 ≤ T.card ∧
      ∀ u ∈ T, ∀ v ∈ T, d.d u v ≤ metricMass d/(2*(Fintype.card V:ℝ)^2)) ∨
    (∃ U : Finset V, (Fintype.card V:ℝ)/3 ≤ U.card ∧
      (U.card:ℝ) ≤ 2*(Fintype.card V:ℝ)/3 ∧
      cutCap N U ≤ 8*(Fintype.card V:ℝ)^2*metricWeight N d*
        Real.log ((Fintype.card V:ℝ)+1)/metricMass d) := by
  classical
  obtain ⟨label,hdiam,hcross⟩ := normalized_partition N hN d hn hA
  by_cases hlarge : ∃ v, 2*(Fintype.card V:ℝ)/3 ≤ (labelFiber label v).card
  · obtain ⟨v,hv⟩ := hlarge
    refine Or.inl ⟨labelFiber label v,⟨v,by simp [labelFiber]⟩,hv,?_⟩
    intro u hu w hw
    apply hdiam
    have hu' : label u = label v := by simpa [labelFiber] using hu
    have hw' : label w = label v := by simpa [labelFiber] using hw
    exact hu'.trans hw'.symm
  · push Not at hlarge
    obtain ⟨U,hU,hl,hh⟩ := balanced_fiber_union label (by omega) hlarge
    exact Or.inr ⟨U,hl,hh,(cutCap_le_crossWeight N label U hU).trans hcross⟩

end LeightonRao.Uniform.Proof
-- End NormalizedPartition

-- Begin SmallMetricCut

namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma small_component_metric_bound (N : Network V) (d : FiniteMetric V)
    (hn : 2 ≤ Fintype.card V) (hA : 0 < metricMass d) (U : Finset V)
    (hlow : (Fintype.card V:ℝ)/3 ≤ U.card)
    (hhigh : (U.card:ℝ) ≤ 2*(Fintype.card V:ℝ)/3)
    (hcap : cutCap N U ≤ 8*(Fintype.card V:ℝ)^2*metricWeight N d*
      Real.log ((Fintype.card V:ℝ)+1)/metricMass d) :
    minCut N*metricMass d ≤ 36*metricWeight N d*Real.log ((Fintype.card V:ℝ)+1) := by
  have hnpos : (0:ℝ)<Fintype.card V := by exact_mod_cast (by omega : 0<Fintype.card V)
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hU : U.Nonempty := Finset.card_pos.mp (by exact_mod_cast (show (0:ℝ)<U.card by linarith))
  have hcc : (Uᶜ.card:ℝ) = (Fintype.card V:ℝ)-(U.card:ℝ) := by
    rw [Finset.card_compl,Nat.cast_sub (Finset.card_le_univ U)]
  have hUc : Uᶜ.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (show (0:ℝ)<Uᶜ.card by rw [hcc]; linarith))
  have hp : 0 < 2*(Fintype.card V:ℝ)^2/9 := by positivity
  have hprod : 2*(Fintype.card V:ℝ)^2/9 ≤ (U.card:ℝ)*(Uᶜ.card:ℝ) := by
    rw [hcc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hhigh)]
  have hbound : minCut N*(2*(Fintype.card V:ℝ)^2/9) ≤
      8*(Fintype.card V:ℝ)^2*metricWeight N d*Real.log ((Fintype.card V:ℝ)+1)/metricMass d :=
    (mul_le_mul_of_nonneg_left hprod (minCut_nonneg N)).trans
      ((minCut_mul_card_le_cutCap N U hU hUc).trans hcap)
  apply (mul_le_mul_iff_left₀ hp).mp
  calc
    minCut N*metricMass d*(2*(Fintype.card V:ℝ)^2/9) =
      (minCut N*(2*(Fintype.card V:ℝ)^2/9))*metricMass d := by ring
    _ ≤ (8*(Fintype.card V:ℝ)^2*metricWeight N d*Real.log ((Fintype.card V:ℝ)+1)/metricMass d)*metricMass d :=
      mul_le_mul_of_nonneg_right hbound hA.le
    _ = (36*metricWeight N d*Real.log ((Fintype.card V:ℝ)+1))*(2*(Fintype.card V:ℝ)^2/9) := by
      rw [div_mul_cancel₀ _ hA.ne']
      ring

lemma log_card_comparison {n : ℕ} (hn : 2 ≤ n) :
    36*Real.log ((n:ℝ)+1) ≤ 100*Real.logb 2 (n:ℝ) := by
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
  have hnpos : (0:ℝ)<n := by linarith
  have hn1 : (1:ℝ)≤n := by linarith
  have hlognonneg := Real.log_nonneg hn1
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogtwo_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hl : Real.log ((n:ℝ)+1) ≤ 2*Real.log (n:ℝ) := by
    calc
      Real.log ((n:ℝ)+1) ≤ Real.log ((n:ℝ)^2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = 2*Real.log (n:ℝ) := by rw [Real.log_pow]; norm_num
  have hratio : Real.log (n:ℝ) ≤ Real.logb 2 (n:ℝ) := by
    rw [Real.logb,le_div_iff₀ hlogtwo]
    exact mul_le_of_le_one_right hlognonneg hlogtwo_le
  have hrnonneg : 0 ≤ Real.logb 2 (n:ℝ) := hlognonneg.trans hratio
  linarith

end LeightonRao.Uniform.Proof
-- End SmallMetricCut

-- Begin MetricRounding

namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma metric_bound_from_large (N : Network V) (hN : IsConnectedNet N)
    (d : FiniteMetric V) (hn : 2 ≤ Fintype.card V)
    (hlarge : ∀ T : Finset V, T.Nonempty → 2*(Fintype.card V:ℝ)/3 ≤ T.card →
      (∀ u ∈ T, ∀ v ∈ T, d.d u v ≤ metricMass d/(2*(Fintype.card V:ℝ)^2)) →
      minCut N*metricMass d ≤ 2*metricWeight N d) :
    minCut N*metricMass d ≤ 100*Real.logb 2 (Fintype.card V:ℝ)*metricWeight N d := by
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (Fintype.card V:ℝ) := by
    rw [Real.logb,le_div_iff₀ hlogtwo,one_mul]
    exact Real.log_le_log (by norm_num) hn2
  have hW := metricWeight_nonneg N d
  by_cases hA : 0 < metricMass d
  · rcases partition_cut_or_large N hN d hn hA with ⟨T,hT,ht,hdiam⟩ | ⟨U,hu,hu',hc⟩
    · exact (hlarge T hT ht hdiam).trans (mul_le_mul_of_nonneg_right (by linarith) hW)
    · have hh := small_component_metric_bound N d hn hA U hu hu' hc
      calc
        minCut N*metricMass d ≤ 36*metricWeight N d*Real.log ((Fintype.card V:ℝ)+1) := hh
        _ = (36*Real.log ((Fintype.card V:ℝ)+1))*metricWeight N d := by ring
        _ ≤ (100*Real.logb 2 (Fintype.card V:ℝ))*metricWeight N d :=
          mul_le_mul_of_nonneg_right (log_card_comparison hn) hW
  · have hz : metricMass d = 0 := le_antisymm (le_of_not_gt hA) (metricMass_nonneg d)
    rw [hz,mul_zero]
    exact mul_nonneg (by linarith) hW

end LeightonRao.Uniform.Proof
-- End MetricRounding

-- Begin CoareaScalar

open Set
open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def scalarSublevel (b : V → ℝ) (r : ℝ) : Finset V :=
  Finset.univ.filter (fun u => b u < r)

noncomputable def scalarEnergy (N : Network V) (b : V → ℝ) (r : ℝ) : ℝ :=
  (1/2)*∑ u, ∑ v, N.C u v * clippedRamp (min (b u) (b v)) (max (b u) (b v)) r

noncomputable def scalarMass (b : V → ℝ) (r : ℝ) : ℝ := ∑ u, clippedRamp 0 (b u) r

omit [DecidableEq V] in
lemma scalarEnergy_continuous (N : Network V) (b : V → ℝ) : Continuous (scalarEnergy N b) := by
  unfold scalarEnergy
  apply continuous_const.mul
  apply continuous_finsetSum
  intro u _
  apply continuous_finsetSum
  intro v _
  exact continuous_const.mul (clippedRamp_continuous _ _)

omit [DecidableEq V] in
lemma scalarMass_continuous (b : V → ℝ) : Continuous (scalarMass b) := by
  exact continuous_finsetSum _ fun u _ => clippedRamp_continuous 0 (b u)

omit [DecidableEq V] in
lemma scalarEnergy_zero (N : Network V) (b : V → ℝ) (hb : ∀ u, 0 ≤ b u) :
    scalarEnergy N b 0 = 0 := by
  have hz (u v : V) : clippedRamp (min (b u) (b v)) (max (b u) (b v)) 0 = 0 :=
    clippedRamp_zero min_le_max (le_min (hb u) (hb v))
  simp [scalarEnergy,hz]

omit [DecidableEq V] in
lemma scalarMass_zero (b : V → ℝ) (hb : ∀ u, 0 ≤ b u) : scalarMass b 0 = 0 := by
  simp [scalarMass, fun u => clippedRamp_zero (hb u) le_rfl]

omit [DecidableEq V] in
lemma scalarMass_top (b : V → ℝ) (hb : ∀ u, 0 ≤ b u) {M : ℝ} (hM : ∀ u, b u ≤ M) :
    scalarMass b M = ∑ u, b u := by
  apply Finset.sum_congr rfl
  intro u _
  simp [clippedRamp, max_eq_left ((hb u).trans (hM u)), min_eq_right (hM u)]

omit [DecidableEq V] in
lemma scalarEnergy_le (N : Network V) (d : FiniteMetric V) (b : V → ℝ)
    (hb : ∀ u v, |b u-b v| ≤ d.d u v) (r : ℝ) : scalarEnergy N b r ≤ metricWeight N d := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (N.C_nonneg u v)
  exact clippedRamp_le.trans ((max_sub_min_eq_abs _ _).trans_le (by simpa [abs_sub_comm] using hb u v))

lemma scalarEnergy_hasDerivAt (N : Network V) (b : V → ℝ) (r : ℝ)
    (hr : ∀ u, r ≠ b u) :
    HasDerivAt (scalarEnergy N b) (cutCap N (scalarSublevel b r)) r := by
  have ht (u v : V) : HasDerivAt
      (fun x => N.C u v * clippedRamp (min (b u) (b v)) (max (b u) (b v)) x)
      (N.C u v * (cutMetric (scalarSublevel b r)).d u v) r := by
    have hmin : r ≠ min (b u) (b v) := by rw [ne_eq,min_def]; split_ifs <;> exact hr _
    have hmax : r ≠ max (b u) (b v) := by rw [ne_eq,max_def]; split_ifs <;> exact hr _
    have h := (clippedRamp_hasDerivAt min_le_max hmin hmax).const_mul (N.C u v)
    rw [minmax_cross_indicator (hr u) (hr v)] at h
    simpa [cutMetric,scalarSublevel] using h
  have h := (HasDerivAt.fun_sum (fun u (_ : u ∈ Finset.univ) =>
    HasDerivAt.fun_sum (fun v (_ : v ∈ Finset.univ) => ht u v))).const_mul (1/2:ℝ)
  change HasDerivAt (scalarEnergy N b) (metricWeight N (cutMetric (scalarSublevel b r))) r at h
  rwa [cutMetric_weight] at h

lemma scalarMass_hasDerivAt (b : V → ℝ) (hb : ∀ u, 0 ≤ b u) {r : ℝ} (hr : 0 < r)
    (hne : ∀ u, r ≠ b u) :
    HasDerivAt (scalarMass b) ((scalarSublevel b r)ᶜ.card : ℝ) r := by
  have ht (u : V) : HasDerivAt (clippedRamp 0 (b u))
      (if u ∈ scalarSublevel b r then 0 else 1) r := by
    have h := clippedRamp_hasDerivAt (hb u) hr.ne' (hne u)
    convert h using 1
    by_cases hlt : b u < r
    · simp [scalarSublevel,hlt,not_lt.mpr hlt.le]
    · have hgt : r < b u := lt_of_le_of_ne (le_of_not_gt hlt) (hne u)
      simp [scalarSublevel,hlt,hr,hgt]
  have h := HasDerivAt.fun_sum (fun u (_ : u ∈ Finset.univ) => ht u)
  rw [sum_ite_mem_const] at h
  convert h using 1 <;> first | rfl | simp

end LeightonRao.Uniform.Proof
-- End CoareaScalar

-- Begin DistanceToSet

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type}

noncomputable def setDistance (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) (u : V) : ℝ :=
  T.inf' hT (fun t => d.d t u)

lemma setDistance_attained (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) (u : V) :
    ∃ t ∈ T, d.d t u = setDistance d T hT u := by
  obtain ⟨t,ht,he⟩ := Finset.exists_mem_eq_inf' hT (fun t => d.d t u)
  exact ⟨t,ht,he.symm⟩

lemma setDistance_nonneg (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) (u : V) :
    0 ≤ setDistance d T hT u := by
  exact Finset.le_inf' hT _ fun t _ => d.nonneg t u

lemma setDistance_zero (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) {u : V} (hu : u ∈ T) :
    setDistance d T hT u = 0 := by
  apply le_antisymm _ (setDistance_nonneg d T hT u)
  exact (Finset.inf'_le _ hu).trans_eq (d.self u)

lemma setDistance_le_add (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) (u v : V) :
    setDistance d T hT u ≤ d.d u v + setDistance d T hT v := by
  obtain ⟨t,ht,he⟩ := setDistance_attained d T hT v
  calc
    _ ≤ d.d t u := Finset.inf'_le _ ht
    _ ≤ d.d t v + d.d v u := d.triangle t v u
    _ = _ := by rw [he,d.symm v u]; ring

lemma setDistance_abs_sub_le (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) (u v : V) :
    |setDistance d T hT u - setDistance d T hT v| ≤ d.d u v := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [setDistance_le_add d T hT u v]
  · have h := setDistance_le_add d T hT v u
    rw [d.symm v u] at h
    linarith

lemma metric_le_setDistance_add (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty)
    {D : ℝ} (hD : ∀ s ∈ T, ∀ t ∈ T, d.d s t ≤ D) (u v : V) :
    d.d u v ≤ setDistance d T hT u + setDistance d T hT v + D := by
  obtain ⟨s,hs,hse⟩ := setDistance_attained d T hT u
  obtain ⟨t,ht,hte⟩ := setDistance_attained d T hT v
  have h1 := d.triangle u s v
  have h2 := d.triangle s t v
  have h3 := hD s hs t ht
  rw [d.symm u s,hse] at h1
  rw [hte] at h2
  linarith

lemma mass_le_setDistance_sum [Fintype V] (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty)
    {D : ℝ} (hD : ∀ s ∈ T, ∀ t ∈ T, d.d s t ≤ D) :
    metricMass d ≤ (Fintype.card V : ℝ) * (∑ u, setDistance d T hT u) +
      (Fintype.card V : ℝ)^2 * D / 2 := by
  have h : (∑ u, ∑ v, d.d u v) ≤
      ∑ u, ∑ v, (setDistance d T hT u + setDistance d T hT v + D) := by
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => metric_le_setDistance_add d T hT hD u v
  calc
    metricMass d ≤ (1/2 : ℝ) * (∑ u, ∑ v, (setDistance d T hT u + setDistance d T hT v + D)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]
      ring

end LeightonRao.Uniform.Proof
-- End DistanceToSet

-- Begin CoareaInequality

open Set
open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]

lemma scalar_coarea_inequality (N : Network V) (d : FiniteMetric V) (b : V → ℝ)
    (hb : ∀ u, 0 ≤ b u) (hlip : ∀ u v, |b u-b v| ≤ d.d u v)
    (T : Finset V) (hT : T.Nonempty) (hzero : ∀ t ∈ T, b t = 0) :
    minCut N * (T.card : ℝ) * (∑ u, b u) ≤ metricWeight N d := by
  classical
  let M : ℝ := 1 + ∑ u, b u
  have hsum : 0 ≤ ∑ u, b u := Finset.sum_nonneg fun u _ => hb u
  have hM : 0 < M := by dsimp [M]; linarith
  have hbM (u : V) : b u ≤ M := by
    have h := Finset.single_le_sum (fun v _ => hb v) (Finset.mem_univ u)
    dsimp [M]; linarith
  let F : ℝ → ℝ := fun r => scalarEnergy N b r - minCut N * (T.card : ℝ) * scalarMass b r
  let G : ℝ → ℝ := fun r => cutCap N (scalarSublevel b r) -
    minCut N * (T.card : ℝ) * ((scalarSublevel b r)ᶜ.card : ℝ)
  have hc : Continuous F := (scalarEnergy_continuous N b).sub
    (continuous_const.mul (scalarMass_continuous b))
  have hd : ∀ r ∈ Ioo 0 M, r ∉ Finset.univ.image b → HasDerivAt F (G r) r := by
    intro r hr hs
    have hne (u : V) : r ≠ b u := by
      intro he
      exact hs (Finset.mem_image.mpr ⟨u,Finset.mem_univ u,he.symm⟩)
    exact (scalarEnergy_hasDerivAt N b r hne).sub
      ((scalarMass_hasDerivAt b hb hr.1 hne).const_mul (minCut N * (T.card : ℝ)))
  have hg : ∀ r ∈ Ioo 0 M, r ∉ Finset.univ.image b → 0 ≤ G r := by
    intro r hr _
    let U := scalarSublevel b r
    have hTU : T ⊆ U := by
      intro t ht
      simp [U,scalarSublevel,hzero t ht,hr.1]
    have hU : U.Nonempty := hT.mono hTU
    have hcard : (T.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hTU
    change 0 ≤ cutCap N U - minCut N * (T.card : ℝ) * (Uᶜ.card : ℝ)
    by_cases hUc : Uᶜ.Nonempty
    · have hcut := minCut_mul_card_le_cutCap N U hU hUc
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (minCut_nonneg N)) (Nat.cast_nonneg Uᶜ.card : (0:ℝ) ≤ _)
      nlinarith
    · have hz : Uᶜ.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hUc)
      simpa [hz] using cutCap_nonneg N U
  have hi := inc_off_finset (Finset.univ.image b) hM hc.continuousOn hd hg
  have hF0 : F 0 = 0 := by simp [F,scalarEnergy_zero N b hb,scalarMass_zero b hb]
  have hFM : F M = scalarEnergy N b M - minCut N * (T.card : ℝ) * (∑ u,b u) := by
    dsimp only [F]
    rw [scalarMass_top b hb hbM]
  rw [hF0,hFM] at hi
  have hbound := scalarEnergy_le N d b hlip M
  linarith

lemma setDistance_coarea (N : Network V) (d : FiniteMetric V) (T : Finset V) (hT : T.Nonempty) :
    minCut N * (T.card : ℝ) * (∑ u, setDistance d T hT u) ≤ metricWeight N d :=
  scalar_coarea_inequality N d (setDistance d T hT) (setDistance_nonneg d T hT)
    (setDistance_abs_sub_le d T hT) T hT (fun _ ht => setDistance_zero d T hT ht)

end LeightonRao.Uniform.Proof
-- End CoareaInequality

-- Begin LargeComponent

open scoped BigOperators
namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]

lemma large_component_metric_bound (N : Network V) (d : FiniteMetric V)
    (hn : 2 ≤ Fintype.card V) (T : Finset V) (hT : T.Nonempty)
    (hlarge : 2*(Fintype.card V : ℝ)/3 ≤ T.card)
    (hdiam : ∀ u ∈ T, ∀ v ∈ T, d.d u v ≤ metricMass d/(2*(Fintype.card V : ℝ)^2)) :
    minCut N * metricMass d ≤ 2 * metricWeight N d := by
  have hnpos : (0:ℝ) < Fintype.card V := by
    have : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hnne : (Fintype.card V : ℝ) ≠ 0 := hnpos.ne'
  have hm := mass_le_setDistance_sum d T hT hdiam
  have he : (Fintype.card V : ℝ)^2 * (metricMass d/(2*(Fintype.card V : ℝ)^2))/2 =
      metricMass d/4 := by field_simp; ring
  rw [he] at hm
  have hB : 0 ≤ ∑ u, setDistance d T hT u :=
    Finset.sum_nonneg fun u _ => setDistance_nonneg d T hT u
  have hs := mul_le_mul_of_nonneg_right hlarge hB
  have hA : metricMass d ≤ 2*(T.card : ℝ)*(∑ u, setDistance d T hT u) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hA (minCut_nonneg N)
  have hc := setDistance_coarea N d T hT
  nlinarith

end LeightonRao.Uniform.Proof
-- End LargeComponent

-- Begin MetricBound

namespace LeightonRao.Uniform.Proof
variable {V : Type} [Fintype V] [DecidableEq V]

lemma metric_cut_bound (N : Network V) (hN : IsConnectedNet N)
    (d : FiniteMetric V) (hn : 2 ≤ Fintype.card V) :
    minCut N*metricMass d ≤ 100*Real.logb 2 (Fintype.card V:ℝ)*metricWeight N d := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact metric_bound_from_large N hN d hn (fun T hT hl hd =>
    large_component_metric_bound N d hn T hT hl hd)

end LeightonRao.Uniform.Proof
-- End MetricBound

-- Begin RootAssembly

open scoped BigOperators
namespace LeightonRao.Uniform
open Proof

theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V),
        2 ≤ Fintype.card V → IsConnectedNet N →
          c * minCut N / Real.logb 2 (Fintype.card V : ℝ) ≤
            maxFlow N uniformDemand ∧
          maxFlow N uniformDemand ≤ minCut N := by
  refine ⟨1/100, by norm_num, ?_⟩
  intro V _ _ N hn hN
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnreal : (1:ℝ) < Fintype.card V := by exact_mod_cast (by omega : 1 < Fintype.card V)
  have hlog : 0 < Real.logb 2 (Fintype.card V : ℝ) :=
    div_pos (Real.log_pos hnreal) (Real.log_pos (by norm_num))
  refine ⟨?_, maxFlow_le_minCut N⟩
  apply le_maxFlow_of_feasible (div_nonneg (mul_nonneg (by norm_num) (minCut_nonneg N)) hlog.le)
  apply exists_flow_of_metric_bound N
    (div_nonneg (mul_nonneg (by norm_num) (minCut_nonneg N)) hlog.le)
  intro d
  have hb := metric_cut_bound N hN d hn
  have he : ((1/100:ℝ)*minCut N/Real.logb 2 (Fintype.card V : ℝ))*metricMass d =
      (minCut N*metricMass d)/(100*Real.logb 2 (Fintype.card V : ℝ)) := by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
  nlinarith

end LeightonRao.Uniform
-- End RootAssembly

-- Begin Solution

open LeightonRao.Uniform

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V),
        2 ≤ Fintype.card V → IsConnectedNet N →
          c * minCut N / Real.logb 2 (Fintype.card V : ℝ) ≤
            maxFlow N uniformDemand ∧
          maxFlow N uniformDemand ≤ minCut N := by
  exact LeightonRao.Uniform.theorem_2
-- End Solution
