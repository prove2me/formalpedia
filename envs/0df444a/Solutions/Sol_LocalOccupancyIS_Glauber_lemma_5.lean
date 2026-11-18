-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:43:45.033934+00:00
-- url     : https://prove2.me/submissions/21f6ad5f-bc34-4286-87fd-f5156f9b56e9

import Definitions.Def_LocalOccupancyIS_Glauber_GraphModel

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Common neighbors of a finite set; internal edges in its parts are unrestricted. -/
def commonFinset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∀ u ∈ S, G.Adj v u)

lemma mem_commonFinset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    v ∈ commonFinset G S ↔ ∀ u ∈ S, G.Adj v u := by simp [commonFinset]

lemma powerset_neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t : ℕ) (v : V) :
    (A ∩ G.neighborFinset v).powersetCard t =
      (A.powersetCard t).filter (fun S => v ∈ commonFinset G S) := by
  ext S
  simp only [Finset.mem_powersetCard, Finset.subset_inter_iff, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hA,hN⟩,hcard⟩
    refine ⟨⟨hA,hcard⟩, (mem_commonFinset G S v).mpr ?_⟩
    intro u hu
    exact (G.mem_neighborFinset v u).mp (hN hu)
  · rintro ⟨⟨hA,hcard⟩,hN⟩
    refine ⟨⟨hA,?_⟩,hcard⟩
    intro u hu
    exact (G.mem_neighborFinset v u).mpr ((mem_commonFinset G S v).mp hN u hu)

lemma binomial_common_double_count (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t : ℕ) :
    (∑ v : V, (A ∩ G.neighborFinset v).card.choose t) =
      ∑ S ∈ A.powersetCard t, (commonFinset G S).card := by
  classical
  simp_rw [← Finset.card_powersetCard, powerset_neighbors, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp

lemma pair_mem_bicliques (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ} (ht : 1 ≤ t)
    {S B : Finset V} (hS : S.card = t) (hB : B.card = t) (hBS : B ⊆ commonFinset G S) :
    {S,B} ∈ bicliques G t ∧ S ≠ B := by
  classical
  have hd : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvB
    exact G.irrefl ((mem_commonFinset G S v).mp (hBS hvB) v hvS)
  have hne : S ≠ B := by
    intro he
    have hemp : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact Finset.disjoint_left.mp hd hv (he ▸ hv)
    rw [hemp, Finset.card_empty] at hS
    omega
  have hadj : ∀ s ∈ S, ∀ b ∈ B, G.Adj s b := by
    intro s hs b hb
    exact ((mem_commonFinset G S b).mp (hBS hb) s hs).symm
  refine ⟨?_,hne⟩
  unfold bicliques
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, by simp [hne], ?_⟩
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl <;> simp [hS, hB]
  · intro C hC E hE hCE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC hE
    rcases hC with rfl | rfl <;> rcases hE with rfl | rfl
    · exact (hCE rfl).elim
    · exact ⟨hd,hadj⟩
    · exact ⟨hd.symm,fun b hb s hs => (hadj s hs b hb).symm⟩
    · exact (hCE rfl).elim

lemma pair_parts_injective {S B S' B' : Finset V} (h : (({S,B} : Finset (Finset V)),S) = (({S',B'} : Finset (Finset V)),S'))
    (hne : S ≠ B) (hne' : S' ≠ B') : (S,B) = (S',B') := by
  have hS : S = S' := congrArg Prod.snd h
  subst S'
  have hC : ({S,B} : Finset (Finset V)) = {S,B'} := congrArg Prod.fst h
  have hmem : B ∈ ({S,B'} : Finset (Finset V)) := hC ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self B))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact (hne hmem.symm).elim
  · subst B'; rfl

lemma common_choose_bound (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {t : ℕ} (ht : 1 ≤ t) :
    (∑ S ∈ A.powersetCard t, (commonFinset G S).card.choose t) ≤ 2*(bicliques G t).card := by
  classical
  let domain := (A.powersetCard t).sigma (fun S => (commonFinset G S).powersetCard t)
  let target := (bicliques G t).sigma (fun C => C)
  have hdomain (x : Σ _ : Finset V, Finset V) (hx : x ∈ domain) :
      {x.1,x.2} ∈ bicliques G t ∧ x.1 ≠ x.2 := by
    obtain ⟨hS,hB⟩ := Finset.mem_sigma.mp hx
    exact pair_mem_bicliques G ht (Finset.mem_powersetCard.mp hS).2
      (Finset.mem_powersetCard.mp hB).2 (Finset.mem_powersetCard.mp hB).1
  have hle : domain.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn
      (fun (x : Σ _ : Finset V, Finset V) =>
        (⟨{x.1,x.2},x.1⟩ : Σ _ : Finset (Finset V), Finset V))
    · intro x hx
      exact Finset.mem_sigma.mpr ⟨(hdomain x hx).1, by simp⟩
    · intro x hx y hy hxy
      have hC := congrArg Sigma.fst hxy
      have hS := congrArg (fun z : Σ _ : Finset (Finset V), Finset V => z.2) hxy
      have hp := pair_parts_injective (Prod.ext hC hS) (hdomain x hx).2 (hdomain y hy).2
      have hx1 : x.1 = y.1 := congrArg Prod.fst hp
      have hx2 : x.2 = y.2 := congrArg Prod.snd hp
      cases x
      cases y
      simp_all
  have heDomain : domain.card = ∑ S ∈ A.powersetCard t, (commonFinset G S).card.choose t := by
    simp [domain, Finset.card_sigma]
  have heTarget : target.card = 2*(bicliques G t).card := by
    rw [show target = (bicliques G t).sigma (fun C => C) from rfl, Finset.card_sigma]
    have hh : (∑ C ∈ bicliques G t, C.card) = ∑ C ∈ bicliques G t, 2 := by
      apply Finset.sum_congr rfl
      intro C hC
      simp only [bicliques, Finset.mem_filter] at hC
      exact hC.2.1
    rw [hh]
    simp [mul_comm]
  rwa [heDomain, heTarget] at hle

lemma subset_degree_double_count (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (∑ v ∈ A, G.degree v) = ∑ v : V, (A ∩ G.neighborFinset v).card := by
  classical
  have hdegree (v : V) : G.degree v = ∑ u : V, if G.Adj v u then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [← SimpleGraph.mem_neighborFinset]
  simp_rw [hdegree]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  have he : A ∩ G.neighborFinset v = A.filter (G.Adj v) := by ext u; simp
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  simp [G.adj_comm]

lemma common_choose_density_bound (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {t : ℕ} (ht : 1 ≤ t) {b : ℝ} (hb : 0 ≤ b) (hd : Density G t b) :
    (∑ S ∈ A.powersetCard t, ((commonFinset G S).card.choose t : ℝ)) ≤
      (b+1)*Fintype.card V := by
  have hcount := common_choose_bound G A ht
  have hr : (∑ S ∈ A.powersetCard t, ((commonFinset G S).card.choose t : ℝ)) ≤
      2*(bicliques G t).card := by exact_mod_cast hcount
  unfold Density at hd
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hN : (0:ℝ) ≤ (bicliques G t).card := Nat.cast_nonneg _
  have hK : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

lemma degree_sum_density_one (G : SimpleGraph V) [DecidableRel G.Adj]
    {b : ℝ} (hd : Density G 1 b) : (∑ v, (G.degree v : ℝ)) ≤ b*Fintype.card V := by
  have hcount := common_choose_bound G Finset.univ (by omega : 1 ≤ 1)
  simp only [Nat.choose_one_right] at hcount
  have hdouble := binomial_common_double_count G Finset.univ 1
  simp only [Nat.choose_one_right, Finset.univ_inter, G.card_neighborFinset_eq_degree] at hdouble
  rw [← hdouble] at hcount
  have hr : (∑ v, (G.degree v : ℝ)) ≤ 2*(bicliques G 1).card := by exact_mod_cast hcount
  unfold Density at hd
  norm_num at hd
  exact hr.trans hd

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma binomial_root_bound (j t : ℕ) (ht : 1 ≤ t) :
    (j:ℝ) ≤ (t:ℝ)-1 + ((t.factorial : ℝ)*j.choose t)^(1/(t:ℝ)) := by
  have ht' : (0:ℝ) < t := by exact_mod_cast ht
  have hn : 0 ≤ (t.factorial : ℝ)*j.choose t := by positivity
  have hnat := Nat.pow_sub_le_descFactorial j t
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hnat
  have hreal : ((j+1-t : ℕ):ℝ)^t ≤ (t.factorial : ℝ)*j.choose t := by exact_mod_cast hnat
  have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ((j+1-t : ℕ):ℝ)^t) hreal
    (show 0 ≤ 1/(t:ℝ) by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel ht'.ne', Real.rpow_one] at hh
  have hj : j ≤ (t-1)+(j+1-t) := by omega
  have hj' : (j:ℝ) ≤ ((t-1:ℕ):ℝ)+((j+1-t:ℕ):ℝ) := by exact_mod_cast hj
  rw [Nat.cast_sub ht, Nat.cast_one] at hj'
  linarith

lemma sum_root_bound {ι : Type} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ S, (f i)^q) ≤ (S.card:ℝ)^(1-q) * (∑ i ∈ S, f i)^q := by
  classical
  by_cases he : S = ∅
  · subst S; simp [Real.zero_rpow hq.ne']
  have hN : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
  have hw : (∑ _ ∈ S, (S.card:ℝ)⁻¹) = 1 := by simp [hN.ne']
  have hh := (Real.concaveOn_rpow hq.le hq1).le_map_sum
    (t := S) (w := fun _ => (S.card:ℝ)⁻¹) (p := f)
    (fun _ _ => (inv_pos.mpr hN).le) hw hf
  simp only [smul_eq_mul] at hh
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hN.le
  calc
    _ = (S.card:ℝ) * ((S.card:ℝ)⁻¹ * ∑ i ∈ S, (f i)^q) := by field_simp
    _ ≤ (S.card:ℝ)*((S.card:ℝ)⁻¹ * ∑ i ∈ S, f i)^q := hh'
    _ = _ := by
      rw [Real.mul_rpow (inv_nonneg.mpr hN.le) (Finset.sum_nonneg hf), Real.inv_rpow hN.le]
      rw [Real.rpow_sub hN, Real.rpow_one]
      ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma factorial_power_bound (t : ℕ) (ht : 2 ≤ t) :
    (t.factorial : ℝ)^(2/(t:ℝ)^2) ≤ t := by
  have ht' : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htwo : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hf : (t.factorial:ℝ) ≤ (t:ℝ)^t := by exact_mod_cast Nat.factorial_le_pow t
  have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ t.factorial) hf
    (show 0 ≤ 2/(t:ℝ)^2 by positivity)
  rw [← Real.rpow_natCast_mul ht'.le] at hh
  have he : (t:ℝ)*(2/(t:ℝ)^2) = 2/(t:ℝ) := by field_simp <;> ring
  rw [he] at hh
  refine hh.trans ?_
  calc
    _ ≤ (t:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ((div_le_one ht').mpr htwo)
    _ = _ := Real.rpow_one _

lemma factorial_R_identity {f R : ℝ} (hf : 0 < f) (hR : 0 < R) {q : ℝ} :
    f^q * (f^q * R^(1-q))^q = f^(2*q^2) * (f*R)^((1-q)*q) := by
  apply Real.log_injOn_pos (by change (0 : ℝ) < _; positivity) (by change (0 : ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  <;> ring

lemma sum_binomial_root_bound {ι : Type} (S : Finset ι) (j : ι → ℕ) {t : ℕ} (ht : 1 ≤ t) :
    (∑ i ∈ S, (j i : ℝ)) ≤ ((t:ℝ)-1)*S.card +
      (t.factorial:ℝ)^(1/(t:ℝ))*(S.card:ℝ)^(1-1/(t:ℝ))*(∑ i ∈ S, (j i).choose t : ℝ)^(1/(t:ℝ)) := by
  have ht' : (0:ℝ) < t := by exact_mod_cast ht
  have hq : 0 < 1/(t:ℝ) := by positivity
  have hq1 : 1/(t:ℝ) ≤ 1 := (div_le_one ht').mpr (by exact_mod_cast ht)
  have hf : 0 < (t.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos t
  have hh := Finset.sum_le_sum (s := S) (fun i _ => binomial_root_bound (j i) t ht)
  simp_rw [Real.mul_rpow hf.le (Nat.cast_nonneg _), Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  have hhold := sum_root_bound S (fun i => ((j i).choose t : ℝ)) (fun _ _ => Nat.cast_nonneg _) hq hq1
  have hhold' := mul_le_mul_of_nonneg_left hhold (Real.rpow_nonneg hf.le (1/(t:ℝ)))
  calc
    _ ≤ _ := hh
    _ ≤ _ := by nlinarith

lemma root_product_expand {f R k B : ℝ} (hf : 0 < f) (hR : 0 < R)
    (hk : 0 < k) (hB : 0 < B) (q : ℝ) :
    f^q*k^(1-q)*(f^q*R^(1-q)*(B*k)^q)^q =
      f^(2*q^2)*k^(1-q+q^2)*B^(q^2)*(f*R)^((1-q)*q) := by
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  <;> ring

lemma root_first_expand {f R k T : ℝ} (hf : 0 < f) (hR : 0 < R)
    (hk : 0 < k) (hT : 1 < T) (q : ℝ) :
    f^q*k^(1-q)*((T-1)*R)^q = (T-1)^q*k^(1-q)*(f*R)^q := by
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  have hTm : 0 < T-1 := by linarith
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  <;> ring

lemma young_density_identity {T s k r : ℝ} (hT : 1 < T) (hs : 0 < s)
    (hk : 0 < k) (hr : 0 < r) :
    T*k^(1-1/T+(1/T)^2)*(s^(2*T-1))^((1/T)^2)*r^(1-1/T) =
      T*(s*k)^(1/T)*(s^(1/T)*k^(1-1/T)*r)^(1-1/T) := by
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  have hTpos : 0 < T := by linarith
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  <;> field_simp
  <;> ring

lemma scale_mix_identity {s k : ℝ} (hs : 0 < s) (hk : 0 < k) (q : ℝ) :
    s^q*k^(1-q) = s*(k/s)^(1-q) := by
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

lemma weighted_from_subsets {V : Type} [Fintype V] [DecidableEq V]
    (d z : V → ℝ) {p C c : ℝ} (hp : 0 ≤ p) (hz : ∀ v, 0 ≤ z v ∧ z v ≤ p)
    (hsub : ∀ A : Finset V, (∑ v ∈ A, d v) ≤ C+c*A.card) :
    (∑ v, d v*z v) ≤ C*p + c*(∑ v, z v) := by
  classical
  let A := Finset.univ.filter (fun v => c < d v)
  have hpos : (∑ v ∈ A, (d v-c)) ≤ C := by
    have hh := hsub A
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hpoint (v : V) : d v*z v ≤ c*z v + p*(if c < d v then d v-c else 0) := by
    split_ifs with hv
    · have hh := mul_le_mul_of_nonneg_left (hz v).2 (sub_nonneg.mpr hv.le)
      nlinarith
    · have hd : d v ≤ c := le_of_not_gt hv
      have hh := mul_le_mul_of_nonneg_right hd (hz v).1
      simpa using hh
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have he : (∑ v, if c < d v then d v-c else 0) = ∑ v ∈ A, (d v-c) := by
    rw [Finset.sum_filter]
  rw [he] at hh
  have hh' := mul_le_mul_of_nonneg_left hpos hp
  nlinarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma two_stage_degree_bound (t : ℕ) (ht : 2 ≤ t) {k r R U B d : ℝ}
    (hk : 0 < k) (hr : 0 < r) (hR : 0 < R) (hU : 0 ≤ U) (hB : 0 < B)
    (hFR : (t.factorial:ℝ)*R ≤ r^t)
    (hd : d ≤ ((t:ℝ)-1)*k + (t.factorial:ℝ)^(1/(t:ℝ))*k^(1-1/(t:ℝ))*U^(1/(t:ℝ)))
    (hupper : U ≤ ((t:ℝ)-1)*R + (t.factorial:ℝ)^(1/(t:ℝ))*R^(1-1/(t:ℝ))*(B*k)^(1/(t:ℝ))) :
    d ≤ ((t:ℝ)-1)*k + ((t:ℝ)-1)^(1/(t:ℝ))*k^(1-1/(t:ℝ))*r +
      t*k^(1-1/(t:ℝ)+(1/(t:ℝ))^2)*B^((1/(t:ℝ))^2)*r^(1-1/(t:ℝ)) := by
  let q : ℝ := 1/(t:ℝ)
  let f : ℝ := t.factorial
  have ht' : (1:ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have ht0 : (0:ℝ) < t := by linarith
  have htwo : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hf : 0 < f := by dsimp [f]; exact_mod_cast Nat.factorial_pos t
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one ht0).mpr (by linarith)
  have ha : 0 ≤ 1-q := by linarith
  have hUroot := Real.rpow_le_rpow hU hupper hq.le
  have hadd := Real.rpow_add_le_add_rpow
    (show 0 ≤ ((t:ℝ)-1)*R by positivity)
    (show 0 ≤ (t.factorial:ℝ)^q*R^(1-q)*(B*k)^q by positivity) hq.le hq1
  have hsplit := mul_le_mul_of_nonneg_left (hUroot.trans hadd)
    (show 0 ≤ f^q*k^(1-q) by positivity)
  have hrootr : (r^t)^q = r := by
    rw [← Real.rpow_natCast_mul hr.le]
    have he : (t:ℝ)*q = 1 := by dsimp [q]; field_simp
    rw [he, Real.rpow_one]
  have hrootra : (r^t)^((1-q)*q) = r^(1-q) := by
    rw [← Real.rpow_natCast_mul hr.le]
    congr 1
    dsimp [q]
    field_simp
    <;> ring
  have hfirst : f^q*k^(1-q)*(((t:ℝ)-1)*R)^q ≤ ((t:ℝ)-1)^q*k^(1-q)*r := by
    rw [root_first_expand hf hR hk ht' q]
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ f*R) hFR hq.le
    rw [hrootr] at hh
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hfac : f^(2*q^2) ≤ (t:ℝ) := by
    convert factorial_power_bound t ht using 1
    dsimp [q]
    congr 1
    field_simp
    <;> ring
  have hsecond : f^q*k^(1-q)*(f^q*R^(1-q)*(B*k)^q)^q ≤
      t*k^(1-q+q^2)*B^(q^2)*r^(1-q) := by
    rw [root_product_expand hf hR hk hB q]
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ f*R) hFR (mul_nonneg ha hq.le)
    rw [hrootra] at hh
    calc
      _ ≤ f^(2*q^2)*k^(1-q+q^2)*B^(q^2)*r^(1-q) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := by
        have hh' := mul_le_mul_of_nonneg_right hfac
          (show 0 ≤ k^(1-q+q^2)*B^(q^2)*r^(1-q) by positivity)
        simpa [mul_assoc] using hh'
  change d ≤ ((t:ℝ)-1)*k + ((t:ℝ)-1)^q*k^(1-q)*r + t*k^(1-q+q^2)*B^(q^2)*r^(1-q)
  change d ≤ ((t:ℝ)-1)*k + f^q*k^(1-q)*U^q at hd
  change f^q*k^(1-q)*U^q ≤ f^q*k^(1-q)*((((t:ℝ)-1)*R)^q + (f^q*R^(1-q)*(B*k)^q)^q) at hsplit
  rw [mul_add] at hsplit
  linarith

lemma finish_subset_degree_bound (t : ℕ) (ht : 2 ≤ t) {k r s d : ℝ}
    (hk : 0 < k) (hr : 0 < r) (hs1 : 1 ≤ s)
    (hd : d ≤ ((t:ℝ)-1)*k + ((t:ℝ)-1)^(1/(t:ℝ))*k^(1-1/(t:ℝ))*r +
      t*k^(1-1/(t:ℝ)+(1/(t:ℝ))^2)*(s^(2*(t:ℝ)-1))^((1/(t:ℝ))^2)*r^(1-1/(t:ℝ))) :
    d ≤ t*s*k + 2*((t:ℝ)-1)*s^(1/(t:ℝ))*k^(1-1/(t:ℝ))*r := by
  have ht' : (1:ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have ht0 : (0:ℝ) < t := by linarith
  have htwo : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hq : 0 ≤ 1/(t:ℝ) := by positivity
  have hq1 : 1/(t:ℝ) ≤ 1 := (div_le_one ht0).mpr (by linarith)
  have htm : 0 ≤ (t:ℝ)-1 := by linarith
  have hfirst : ((t:ℝ)-1)^(1/(t:ℝ)) ≤ ((t:ℝ)-1)*s^(1/(t:ℝ)) := by
    have hh : ((t:ℝ)-1)^(1/(t:ℝ)) ≤ (t:ℝ)-1 := by
      calc
        _ ≤ ((t:ℝ)-1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hq1
        _ = _ := Real.rpow_one _
    have hh' := mul_le_mul_of_nonneg_left (Real.one_le_rpow hs1 hq) htm
    linarith
  have hfirst' := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ k^(1-1/(t:ℝ))*r by positivity)
  have hAM := Real.geom_mean_le_arith_mean2_weighted hq (show 0 ≤ 1-1/(t:ℝ) by linarith)
    (show 0 ≤ s*k by positivity) (show 0 ≤ s^(1/(t:ℝ))*k^(1-1/(t:ℝ))*r by positivity)
    (by ring : 1/(t:ℝ)+(1-1/(t:ℝ)) = 1)
  have hAM' := mul_le_mul_of_nonneg_left hAM ht0.le
  have hAMeq : (t:ℝ)*(1/(t:ℝ)*(s*k) + (1-1/(t:ℝ))*(s^(1/(t:ℝ))*k^(1-1/(t:ℝ))*r)) =
      s*k + ((t:ℝ)-1)*s^(1/(t:ℝ))*k^(1-1/(t:ℝ))*r := by field_simp <;> ring
  rw [← mul_assoc, ← young_density_identity ht' hs hk hr, hAMeq] at hAM'
  have hbase : ((t:ℝ)-1)*k + s*k ≤ t*s*k := by
    nlinarith [mul_nonneg htm (mul_nonneg (sub_nonneg.mpr hs1) hk.le)]
  nlinarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma density_subset_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : 2 ≤ t) (b : ℝ) (hb : 0 ≤ b) (hk : 1 ≤ Fintype.card V)
    (hd : Density G t b) (A : Finset V) :
    let s : ℝ := (b+1)^(1/(2*(t:ℝ)-1))
    (∑ v ∈ A, (G.degree v : ℝ)) ≤ t*s*Fintype.card V +
      2*((t:ℝ)-1)*s^(1/(t:ℝ))*(Fintype.card V : ℝ)^(1-1/(t:ℝ))*A.card := by
  classical
  dsimp only
  let s : ℝ := (b+1)^(1/(2*(t:ℝ)-1))
  let k : ℝ := Fintype.card V
  have ht2 : (2:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith
  have htm : 0 ≤ (t:ℝ)-1 := by linarith
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  have hB : 0 < b+1 := by linarith
  have hs : 0 < s := Real.rpow_pos_of_pos hB _
  have hs1 : 1 ≤ s := Real.one_le_rpow (by linarith) (by positivity)
  have hk0 : 0 < k := by dsimp [k]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hdouble : (∑ v ∈ A, (G.degree v : ℝ)) = ∑ v : V, ((A ∩ G.neighborFinset v).card:ℝ) := by
    exact_mod_cast subset_degree_double_count G A
  by_cases hsmall : A.card < t
  · have hr : (A.card:ℝ) ≤ (t:ℝ)-1 := by
      have hh : A.card+1 ≤ t := hsmall
      have hh' : (A.card:ℝ)+1 ≤ t := by exact_mod_cast hh
      linarith
    have hsum : (∑ v ∈ A, (G.degree v : ℝ)) ≤ k*A.card := by
      rw [hdouble]
      calc
        _ ≤ ∑ _ : V, (A.card:ℝ) := Finset.sum_le_sum (fun v _ => by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := G.neighborFinset v)))
        _ = _ := by simp [k]
    have hbase : k*A.card ≤ t*s*k := by
      have h1 := mul_le_mul_of_nonneg_left hr hk0.le
      have h2 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ (t:ℝ)*k by positivity)
      nlinarith
    have hrem : 0 ≤ 2*((t:ℝ)-1)*s^(1/(t:ℝ))*k^(1-1/(t:ℝ))*A.card := by positivity
    change (∑ v ∈ A, (G.degree v:ℝ)) ≤ t*s*k + _
    linarith
  · have hrNat : t ≤ A.card := Nat.le_of_not_gt hsmall
    have hr : (0:ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
    let R : ℝ := (A.powersetCard t).card
    let U : ℝ := ∑ v : V, ((A ∩ G.neighborFinset v).card.choose t:ℝ)
    have hR : 0 < R := by
      dsimp [R]
      rw [Finset.card_powersetCard]
      exact_mod_cast Nat.choose_pos hrNat
    have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hFR : (t.factorial:ℝ)*R ≤ (A.card:ℝ)^t := by
      dsimp [R]
      rw [Finset.card_powersetCard]
      have hh := Nat.choose_le_pow_div (α := ℝ) t A.card
      have hf : (0:ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
      have hh' := (le_div_iff₀ hf).mp hh
      simpa [mul_comm] using hh'
    have hd' := sum_binomial_root_bound Finset.univ (fun v : V => (A ∩ G.neighborFinset v).card) (by omega : 1 ≤ t)
    simp only [Finset.card_univ] at hd'
    rw [← hdouble] at hd'
    have hUeq : U = ∑ S ∈ A.powersetCard t, ((commonFinset G S).card:ℝ) := by
      dsimp [U]
      exact_mod_cast binomial_common_double_count G A t
    have hUpper := sum_binomial_root_bound (A.powersetCard t) (fun S => (commonFinset G S).card) (by omega : 1 ≤ t)
    rw [← hUeq] at hUpper
    have hCount := common_choose_density_bound G A (by omega : 1 ≤ t) hb hd
    have hCountRoot := Real.rpow_le_rpow
      (show 0 ≤ ∑ S ∈ A.powersetCard t, ((commonFinset G S).card.choose t:ℝ) by positivity)
      hCount (show 0 ≤ 1/(t:ℝ) by positivity)
    have hUpper' : U ≤ ((t:ℝ)-1)*R + (t.factorial:ℝ)^(1/(t:ℝ))*R^(1-1/(t:ℝ))*((b+1)*k)^(1/(t:ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hCountRoot
        (show 0 ≤ (t.factorial:ℝ)^(1/(t:ℝ))*R^(1-1/(t:ℝ)) by positivity)
      change U ≤ ((t:ℝ)-1)*R + (t.factorial:ℝ)^(1/(t:ℝ))*R^(1-1/(t:ℝ))*_ at hUpper
      linarith
    have htwo := two_stage_degree_bound t ht hk0 hr hR hU hB hFR hd' hUpper'
    have heB : b+1 = s^(2*(t:ℝ)-1) := by
      dsimp [s]
      rw [← Real.rpow_mul hB.le]
      have he : 1/(2*(t:ℝ)-1)*(2*(t:ℝ)-1) = 1 := by field_simp
      rw [he, Real.rpow_one]
    rw [heB] at htwo
    exact finish_subset_degree_bound t ht hk0 hr hs1 htwo

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma lemma5_one (F : SimpleGraph V) [DecidableRel F.Adj] (b : ℝ) (hb : 0 ≤ b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F 1 b) (p₀ : ℝ) (z : V → ℝ)
    (hz : ∀ v, 0 ≤ z v ∧ z v ≤ p₀) :
    (∑ v, (F.degree v:ℝ)*z v) ≤ 4*(b+1)*p₀*Fintype.card V + 4*(b+1)*(∑ v,z v) ∧
    avgDegree F+1 ≤ 4*(b+1) := by
  classical
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have hp : 0 ≤ p₀ := (hz v).1.trans (hz v).2
  have hZ : 0 ≤ ∑ v,z v := Finset.sum_nonneg (fun v _ => (hz v).1)
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hdegree := degree_sum_density_one F hd
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
      mul_le_mul_of_nonneg_left (hz v).2 (Nat.cast_nonneg (F.degree v) : (0:ℝ) ≤ _))
    rw [← Finset.sum_mul] at hh
    have hh' := mul_le_mul_of_nonneg_right hdegree hp
    have hbase : 0 ≤ (b+1)*p₀*Fintype.card V := by positivity
    have hrem : 0 ≤ 4*(b+1)*(∑ v,z v) := by positivity
    have hsmall : p₀*b*Fintype.card V ≤ (b+1)*p₀*Fintype.card V := by nlinarith [mul_nonneg hp hN.le]
    nlinarith
  · have havg : avgDegree F ≤ b := by
      unfold avgDegree
      exact (div_le_iff₀ hN).mpr hdegree
    linarith

lemma lemma5_two (F : SimpleGraph V) [DecidableRel F.Adj] (t : ℕ) (ht : 2 ≤ t)
    (b : ℝ) (hb : 0 ≤ b) (hk : 1 ≤ Fintype.card V) (hd : Density F t b)
    (p₀ : ℝ) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v ∧ z v ≤ p₀) :
    let s : ℝ := (b+1)^(1/(2*(t:ℝ)-1))
    (∑ v, (F.degree v:ℝ)*z v) ≤ 4*t*s*p₀*Fintype.card V +
      4*t*s^(1/(t:ℝ))*(Fintype.card V:ℝ)^(1-1/(t:ℝ))*(∑ v,z v) ∧
    avgDegree F+1 ≤ 4*t*s*max 1 (((Fintype.card V:ℝ)/s)^(1-1/(t:ℝ))) := by
  classical
  dsimp only
  let s : ℝ := (b+1)^(1/(2*(t:ℝ)-1))
  let K : ℝ := Fintype.card V
  let q : ℝ := 1/(t:ℝ)
  let c : ℝ := 2*((t:ℝ)-1)*s^q*K^(1-q)
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have hp : 0 ≤ p₀ := (hz v).1.trans (hz v).2
  have hZ : 0 ≤ ∑ v,z v := Finset.sum_nonneg (fun v _ => (hz v).1)
  have hK : 0 < K := by dsimp [K]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have ht2 : (2:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith
  have htm : 0 ≤ (t:ℝ)-1 := by linarith
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  have hs : 0 < s := Real.rpow_pos_of_pos (by linarith) _
  have hs1 : 1 ≤ s := Real.one_le_rpow (by linarith) (by positivity)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsub (A : Finset V) : (∑ v ∈ A, (F.degree v:ℝ)) ≤ t*s*K+c*A.card := by
    exact density_subset_degree F t ht b hb hk hd A
  constructor
  · have hw := weighted_from_subsets (fun v => (F.degree v:ℝ)) z hp hz hsub
    have hcoef : c ≤ 4*t*s^q*K^(1-q) := by
      have hh := mul_le_mul_of_nonneg_right (show 2*((t:ℝ)-1) ≤ 4*t by linarith)
        (show 0 ≤ s^q*K^(1-q) by positivity)
      simpa [c, mul_assoc] using hh
    have hcoef' := mul_le_mul_of_nonneg_right hcoef hZ
    have hbase : 0 ≤ (t:ℝ)*s*p₀*K := by positivity
    change (∑ v, (F.degree v:ℝ)*z v) ≤ 4*t*s*p₀*K + 4*t*s^q*K^(1-q)*(∑ v,z v)
    nlinarith
  · have hall := hsub Finset.univ
    simp only [Finset.card_univ] at hall
    have havg : avgDegree F ≤ t*s+c := by
      unfold avgDegree
      apply (div_le_iff₀ hK).mpr
      change (∑ v, (F.degree v:ℝ)) ≤ t*s*K+c*K at hall
      nlinarith
    let R := (K/s)^(1-q)
    let M := max 1 R
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMR : R ≤ M := le_max_right _ _
    have hM : 0 ≤ M := by linarith
    have hsm : 1 ≤ s*M := by nlinarith
    have hterm1 : (t:ℝ)*s ≤ t*s*M := by nlinarith [mul_nonneg (show 0 ≤ (t:ℝ)*s by positivity) (sub_nonneg.mpr hM1)]
    have hterm2 : 2*((t:ℝ)-1)*s*R ≤ 2*((t:ℝ)-1)*s*M :=
      mul_le_mul_of_nonneg_left hMR (by positivity)
    have he : c = 2*((t:ℝ)-1)*s*R := by
      dsimp [c, R]
      rw [mul_assoc, scale_mix_identity hs hK q]
      ring
    rw [he] at havg
    change avgDegree F+1 ≤ 4*t*s*M
    have hpositive : 0 ≤ ((t:ℝ)+1)*s*M := by positivity
    nlinarith

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (t : ℕ) (ht : 1 ≤ t)
    (b : ℝ) (hb : 0 ≤ b) (hk : 1 ≤ Fintype.card V) (hd : Density F t b)
    (p₀ : ℝ) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v ∧ z v ≤ p₀) :
    let s : ℝ := (b + 1) ^ (1 / (2 * (t : ℝ) - 1))
    (∑ v, (F.degree v : ℝ) * z v) ≤
      4 * t * s * p₀ * Fintype.card V +
        4 * t * s ^ (1 / (t : ℝ)) * (Fintype.card V : ℝ) ^ (1 - 1 / (t : ℝ)) * (∑ v, z v) ∧
    avgDegree F + 1 ≤ 4 * t * s * max 1 (((Fintype.card V : ℝ) / s) ^ (1 - 1 / (t : ℝ))) := by
  by_cases ht1 : t = 1
  · subst t
    convert lemma5_one F b hb hk hd p₀ z hz using 1 <;> norm_num
  · exact lemma5_two F t (by omega) b hb hk hd p₀ z hz
