-- Prove2me | solution 1 for MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ceccbb13-29a3-54ad-9762-71cdb188ea58

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval hasSubst_elim"
p2m_open "MvFormalGroup"

open MvPowerSeries MvPowerSeries.WithPiTopology Filter

section AdicEvalFinite

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero (x : σ → S) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) (r : MvPolynomial σ R) :
    MvPolynomial.eval₂ (algebraMap R S) x r =
      ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  change ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) = _
  have h1 : ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => by
      rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]
  have h2 : ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => by
      rw [hT m hm, mul_zero]
  rw [h1, h2]

theorem adicEval_eq_aeval_of_forall_prod_eq_zero
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (q : MvPolynomial σ R) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0)
    (hq : ∀ m ∈ T, MvPolynomial.coeff m q = MvPowerSeries.coeff m F) :
    adicEval J x F = MvPolynomial.aeval x q := by
  classical
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : T2Space S := (IsAdic.isHausdorff_iff (show IsAdic J from rfl)).mp hJ

  set c : S := ∑ m ∈ T, algebraMap R S (MvPowerSeries.coeff m F) * m.prod (fun s e => x s ^ e)
    with hc
  have key : ∀ r : MvPolynomial σ R,
      (∀ m ∈ T, MvPolynomial.coeff m r = MvPowerSeries.coeff m F) →
      MvPolynomial.eval₂ (algebraMap R S) x r = c := fun r hr => by
    rw [mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero x T hT r, hc]
    exact Finset.sum_congr rfl fun m hm => by rw [hr m hm]
  rw [MvPolynomial.aeval_def, key q hq]
  change MvPowerSeries.eval₂ (algebraMap R S) x F = c
  unfold MvPowerSeries.eval₂
  split_ifs with H
  · refine key _ fun m _ => ?_
    rw [← MvPolynomial.coeff_coe, H.choose_spec]
  · refine MvPolynomial.toMvPowerSeries_isDenseInducing.extend_eq_of_tendsto ?_
    have hU : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} ∈
        nhds F := by
      have : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} =
          ⋂ m ∈ T, {G : MvPowerSeries σ R | MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} := by
        ext G
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this, Filter.biInter_finset_mem]
      intro m _
      exact ((isOpen_discrete ({MvPowerSeries.coeff m F} : Set R)).preimage
        (continuous_coeff (R := R) m)).mem_nhds rfl
    refine Filter.Tendsto.congr' (Filter.mem_of_superset (Filter.preimage_mem_comap hU)
      fun r hr => ?_) tendsto_const_nhds
    exact (key r fun m hm => by rw [← MvPolynomial.coeff_coe]; exact hr m hm).symm

theorem adicEval_eq_adicEval_bot_of_forall_prod_eq_zero
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (T : Finset (σ →₀ ℕ)) (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) :
    adicEval J x F = adicEval ⊥ x F := by
  classical
  have hq : ∀ m ∈ T, MvPolynomial.coeff m (∑ n ∈ T, MvPolynomial.monomial n (MvPowerSeries.coeff n F)) =
      MvPowerSeries.coeff m F := fun m hm => by
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m (fun n _ hnm => by
      rw [MvPolynomial.coeff_monomial, if_neg hnm]) (fun h => absurd hm h),
      MvPolynomial.coeff_monomial, if_pos rfl]
  rw [adicEval_eq_aeval_of_forall_prod_eq_zero J hJ x F _ T hT hq,
    adicEval_eq_aeval_of_forall_prod_eq_zero ⊥ inferInstance x F _ T hT hq]

theorem adicEval_eq_aeval_of_degree [Finite σ]
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (q : MvPolynomial σ R) (N : ℕ)
    (hx : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0)
    (hq : ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m q = MvPowerSeries.coeff m F) :
    adicEval J x F = MvPolynomial.aeval x q := by
  classical
  haveI := Fintype.ofFinite σ
  let d : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  have hd : ∀ s, d s = N := fun _ => rfl
  let T : Finset (σ →₀ ℕ) := (Finset.Iic d).filter fun m => m.degree < N
  have hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0 := by
    intro m hm
    refine hx m (not_lt.1 fun hlt => hm ?_)
    refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 ?_, hlt⟩
    intro s
    rw [hd]
    exact ((Finsupp.le_degree s m).trans hlt.le)
  exact adicEval_eq_aeval_of_forall_prod_eq_zero J hJ x F q T hT
    fun m hm => hq m (Finset.mem_filter.1 hm).2

theorem exists_forall_degree_le_prod_eq_zero_of_isNilpotent [Finite σ]
    (x : σ → S) (hx : ∀ s, IsNilpotent (x s)) :
    ∃ N : ℕ, ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0 := by
  classical
  haveI := Fintype.ofFinite σ
  choose k hk using hx
  refine ⟨∑ s, (k s + 1) + 1, fun m hm => ?_⟩

  have hlt : ∑ s, (k s + 1) < ∑ s, m s := by
    rw [← Finsupp.degree_eq_sum]; exact Nat.lt_of_succ_le hm
  obtain ⟨s, -, hs⟩ := Finset.exists_lt_of_sum_lt hlt
  have hms : s ∈ m.support := Finsupp.mem_support_iff.2 (by omega)
  refine Finset.prod_eq_zero hms ?_
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hs.le
  change x s ^ m s = 0
  rw [hr, pow_add, pow_succ, hk s, zero_mul, zero_mul]

end AdicEvalFinite

theorem isHausdorff_span_natCast_of_free
    {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hO : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞]
    (g : Type*) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] :
    IsHausdorff (Ideal.span {(p : g)}) g := by
  classical
  let b := Module.Free.chooseBasis 𝓞 g
  refine ⟨fun y hy => ?_⟩
  refine b.ext_elem_iff.2 fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus hO _ fun n => ?_
  have hyn := hy n
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton'] at hyn ⊢
  obtain ⟨z, hz⟩ := hyn
  refine ⟨b.repr z i, ?_⟩
  have : y = ((p : 𝓞) ^ n) • z := by
    rw [← hz, Algebra.smul_def, map_pow, map_natCast, mul_comm]
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

end MvFormalGroup

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval hasSubst_elim"
p2m_open "MvFormalGroup"

open MvPowerSeries

section Packaged

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem exists_finset_of_forall_degree_le_prod_eq_zero [Finite σ] (x : σ → S) (N : ℕ)
    (hx : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) ∧
      ∀ m ∈ T, m.degree < N := by
  classical
  haveI := Fintype.ofFinite σ
  let d : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  have hd : ∀ s, d s = N := fun _ => rfl
  refine ⟨(Finset.Iic d).filter fun m => m.degree < N, fun m hm => ?_,
    fun m hm => (Finset.mem_filter.1 hm).2⟩
  refine hx m (not_lt.1 fun hlt => hm ?_)
  refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 fun s => ?_, hlt⟩
  rw [hd]
  exact (Finsupp.le_degree s m).trans hlt.le

theorem adicEval_span_natCast_eq_adicEval_bot_of_isNilpotent
    {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {g : Type*} [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g]
    {σ : Type*} [Finite σ] {w : σ → g} (hw : ∀ s, IsNilpotent (w s)) (F : MvPowerSeries σ 𝓞) :
    adicEval (Ideal.span {(p : g)}) w F = adicEval ⊥ w F := by
  obtain ⟨N, hN⟩ := exists_forall_degree_le_prod_eq_zero_of_isNilpotent w hw
  obtain ⟨T, hT, -⟩ := exists_finset_of_forall_degree_le_prod_eq_zero w N hN
  exact adicEval_eq_adicEval_bot_of_forall_prod_eq_zero _
    (isHausdorff_span_natCast_of_free (𝓞 := 𝓞) p g) w F T hT

theorem eq_zero_or_eq_single_of_degree_lt_two {τ : Type*} (d : τ →₀ ℕ) (hd : d.degree < 2) :
    d = 0 ∨ ∃ t, d = Finsupp.single t 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.2 h0
  have ht' : d t ≠ 0 := Finsupp.mem_support_iff.1 ht
  refine Or.inr ⟨t, Finsupp.ext fun s => ?_⟩
  by_cases hs : s = t
  · subst hs
    have := Finsupp.le_degree s d
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hs]
    by_contra hds
    have hsub : ({s, t} : Finset τ) ⊆ d.support := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Finsupp.mem_support_iff.2 hds
      · rw [Finset.mem_singleton.1 hi]; exact ht
    have h2 : d s + d t ≤ d.degree := by
      rw [Finsupp.degree_apply, ← Finset.sum_pair hs]
      exact Finset.sum_le_sum_of_subset hsub
    omega

theorem adicEval_bot_eq_of_linear
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {τ σ : Type*} [Fintype τ] [DecidableEq σ]
    (ι : τ → σ) (hι : Function.Injective ι) (v : τ → A)
    (hv : ∀ m : τ →₀ ℕ, 2 ≤ m.degree → m.prod (fun t e => v t ^ e) = 0)
    (w : σ → A) (hwι : ∀ t, w (ι t) = v t) (hw0 : ∀ s, s ∉ Set.range ι → w s = 0)
    (F : MvPowerSeries σ R) :
    adicEval ⊥ w F = algebraMap R A (MvPowerSeries.coeff (0 : σ →₀ ℕ) F)
      + ∑ t, MvPowerSeries.coeff (Finsupp.single (ι t) 1) F • v t := by
  classical

  let T : Finset (σ →₀ ℕ) := insert 0 (Finset.univ.image fun t => Finsupp.single (ι t) 1)
  have hT : ∀ m, m ∉ T → m.prod (fun s e => w s ^ e) = 0 := by
    intro m hm
    by_cases hsupp : ∃ s ∈ m.support, s ∉ Set.range ι
    · obtain ⟨s, hs, hsι⟩ := hsupp
      refine Finset.prod_eq_zero hs ?_
      change w s ^ m s = 0
      rw [hw0 s hsι, zero_pow (Finsupp.mem_support_iff.1 hs)]
    · push Not at hsupp
      have hsub : ↑m.support ⊆ Set.range ι := fun s hs => hsupp s hs
      set m' : τ →₀ ℕ := Finsupp.comapDomain ι m hι.injOn with hm'
      have hmm' : Finsupp.mapDomain ι m' = m := Finsupp.mapDomain_comapDomain ι hι m hsub
      have hprod : m.prod (fun s e => w s ^ e) = m'.prod (fun t e => v t ^ e) := by
        conv_lhs => rw [← hmm']
        rw [Finsupp.prod_mapDomain_index_inj hι]
        exact Finset.prod_congr rfl fun t _ => by simp only [hwι]
      rw [hprod]
      by_cases hdeg : 2 ≤ m'.degree
      · exact hv m' hdeg
      · exfalso
        rcases eq_zero_or_eq_single_of_degree_lt_two m' (not_le.1 hdeg) with h | ⟨t, h⟩
        · apply hm
          rw [← hmm', h, Finsupp.mapDomain_zero]
          exact Finset.mem_insert_self _ _
        · apply hm
          rw [← hmm', h, Finsupp.mapDomain_single]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ t))

  let q : MvPolynomial σ R := MvPolynomial.C (MvPowerSeries.coeff (0 : σ →₀ ℕ) F) +
    ∑ t, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single (ι t) 1) F) * MvPolynomial.X (ι t)
  have hq0 : MvPolynomial.coeff 0 q = MvPowerSeries.coeff (0 : σ →₀ ℕ) F := by
    simp only [q, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_true, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero_X, mul_zero, Finset.sum_const_zero, add_zero]
  have hq1 : ∀ t, MvPolynomial.coeff (Finsupp.single (ι t) 1) q =
      MvPowerSeries.coeff (Finsupp.single (ι t) 1) F := by
    intro t
    have hne : (0 : σ →₀ ℕ) ≠ Finsupp.single (ι t) 1 :=
      (Finsupp.single_ne_zero.2 one_ne_zero).symm
    simp only [q, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_neg hne, zero_add,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    rw [Finset.sum_eq_single t]
    · rw [if_pos rfl, mul_one]
    · intro t' _ ht'
      rw [if_neg, mul_zero]
      intro h
      exact ht' (hι ((Finsupp.single_left_inj one_ne_zero).1 h))
    · intro h; exact absurd (Finset.mem_univ t) h
  have hq : ∀ m ∈ T, MvPolynomial.coeff m q = MvPowerSeries.coeff m F := by
    intro m hm
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact hq0
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hm
      exact hq1 t
  rw [adicEval_eq_aeval_of_forall_prod_eq_zero ⊥ inferInstance w F q T hT hq]
  simp only [q, map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hwι,
    Algebra.smul_def]

end Packaged

end MvFormalGroup

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval hasSubst_elim"
p2m_open "MvFormalGroup"

open MvPowerSeries

section SubstTransfer

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem mem_radical_bot_of_isNilpotent {x : S} (hx : IsNilpotent x) : x ∈ (⊥ : Ideal S).radical := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [hk]; exact Submodule.zero_mem _⟩

theorem adicEval_bot_subst {σ τ : Type*} [Finite σ] {x : σ → S} (hx : ∀ s, IsNilpotent (x s))
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) (f : MvPowerSeries τ R) :
    adicEval ⊥ x (subst a f) = adicEval ⊥ (fun t => adicEval ⊥ x (a t)) f :=
  adicEval_subst ⊥ (fun s => mem_radical_bot_of_isNilpotent (hx s)) ha f

variable {d : ℕ} (Φ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)

theorem adicEval_bot_subst_assoc_left (hΦ : ∀ i, (Φ i).constantCoeff = 0)
    {w : Fin d ⊕ (Fin d ⊕ Fin d) → S} (hw : ∀ s, IsNilpotent (w s)) (i : Fin d) :
    adicEval ⊥ w
      (subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (Φ j))
          fun j => X (Sum.inr (Sum.inr j)))
        (Φ i))
    = adicEval ⊥
        (Sum.elim
          (fun j => adicEval ⊥ (Sum.elim (fun l => w (Sum.inl l)) fun l => w (Sum.inr (Sum.inl l))) (Φ j))
          fun j => w (Sum.inr (Sum.inr j)))
        (Φ i) := by
  have hB0 : ∀ s, (Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
      (fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> exact constantCoeff_X _
  have hB : HasSubst (Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
      fun l => X (Sum.inr (Sum.inl l))) :=
    hasSubst_of_constantCoeff_zero hB0
  have hA : HasSubst (Sum.elim
      (fun j => subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        (Φ j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) :=
    hasSubst_elim (fun j => constantCoeff_subst_eq_zero hB hB0 (hΦ j)) fun j => constantCoeff_X _
  rw [adicEval_bot_subst hw hA]
  congr 1
  funext s
  rcases s with j | j
  · simp only [Sum.elim_inl]
    rw [adicEval_bot_subst hw hB]
    congr 1
    funext l
    rcases l with l | l <;> simp only [Sum.elim_inl, Sum.elim_inr, adicEval_X]
  · simp only [Sum.elim_inr, adicEval_X]

theorem adicEval_bot_subst_assoc_right (hΦ : ∀ i, (Φ i).constantCoeff = 0)
    {w : Fin d ⊕ (Fin d ⊕ Fin d) → S} (hw : ∀ s, IsNilpotent (w s)) (i : Fin d) :
    adicEval ⊥ w
      (subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (Φ j))
        (Φ i))
    = adicEval ⊥
        (Sum.elim
          (fun j => w (Sum.inl j))
          fun j => adicEval ⊥ (Sum.elim (fun l => w (Sum.inr (Sum.inl l))) fun l => w (Sum.inr (Sum.inr l))) (Φ j))
        (Φ i) := by
  have hC0 : ∀ s, (Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
      (fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> exact constantCoeff_X _
  have hC : HasSubst (Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
      fun l => X (Sum.inr (Sum.inr l))) :=
    hasSubst_of_constantCoeff_zero hC0
  have hA : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
      fun j => subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        (Φ j)) :=
    hasSubst_elim (fun j => constantCoeff_X _) fun j => constantCoeff_subst_eq_zero hC hC0 (hΦ j)
  rw [adicEval_bot_subst hw hA]
  congr 1
  funext s
  rcases s with j | j
  · simp only [Sum.elim_inl, adicEval_X]
  · simp only [Sum.elim_inr]
    rw [adicEval_bot_subst hw hC]
    congr 1
    funext l
    rcases l with l | l <;> simp only [Sum.elim_inl, Sum.elim_inr, adicEval_X]

theorem adicEval_bot_subst_swap {v : Fin d ⊕ Fin d → S} (hv : ∀ s, IsNilpotent (v s))
    (i : Fin d) :
    adicEval ⊥ v
      (subst
        (Sum.elim
          (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
          fun j => X (Sum.inl j))
        (Φ i))
    = adicEval ⊥ (Sum.elim (fun j => v (Sum.inr j)) fun j => v (Sum.inl j)) (Φ i) := by
  have hA : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_elim (fun j => constantCoeff_X _) fun j => constantCoeff_X _
  rw [adicEval_bot_subst hv hA]
  congr 1
  funext s
  rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, adicEval_X]

end SubstTransfer

end MvFormalGroup

open MvPowerSeries

noncomputable section

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval hasSubst_elim"
namespace NaturalLaw
p2m_open "MvFormalGroup"

section Trunc

variable (σ : Type*) (R : Type*) [CommRing R]

def truncIdeal (N : ℕ) : Ideal (MvPolynomial σ R) where
  carrier := {f | ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = 0}
  zero_mem' := fun m _ => MvPolynomial.coeff_zero m
  add_mem' := fun {f g} hf hg m hm => by
    rw [MvPolynomial.coeff_add, hf m hm, hg m hm, add_zero]
  smul_mem' := fun h f hf m hm => by
    classical
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hle : x.2.degree ≤ m.degree := by
      rw [← hx, map_add]
      exact le_add_self
    rw [hf x.2 (lt_of_le_of_lt hle hm), mul_zero]

abbrev TruncAlg (N : ℕ) : Type _ := MvPolynomial σ R ⧸ truncIdeal σ R N

def DegLT (N : ℕ) : Type _ := {m : σ →₀ ℕ // m.degree < N}

scoped instance instFiniteDegLT [Finite σ] (N : ℕ) : Finite (DegLT σ N) :=
  (Finsupp.finite_of_degree_lt (σ := σ) N).to_subtype

variable {σ R}

theorem mem_truncIdeal {N : ℕ} {f : MvPolynomial σ R} :
    f ∈ truncIdeal σ R N ↔ ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = 0 :=
  Iff.rfl

def coeffsLT (N : ℕ) : MvPolynomial σ R →ₗ[R] (DegLT σ N → R) where
  toFun f m := MvPolynomial.coeff m.1 f
  map_add' f g := by
    funext m
    exact MvPolynomial.coeff_add m.1 f g
  map_smul' r f := by
    funext m
    rw [RingHom.id_apply, Pi.smul_apply, MvPolynomial.coeff_smul]

theorem coeffsLT_apply (N : ℕ) (f : MvPolynomial σ R) (m : DegLT σ N) :
    coeffsLT N f m = MvPolynomial.coeff m.1 f :=
  rfl

theorem ker_coeffsLT (N : ℕ) :
    LinearMap.ker (coeffsLT (σ := σ) (R := R) N) = (truncIdeal σ R N).restrictScalars R := by
  ext f
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_truncIdeal]
  constructor
  · intro h m hm
    exact congrFun h ⟨m, hm⟩
  · intro h
    funext m
    exact h m.1 m.2

theorem coeffsLT_surjective [Finite σ] (N : ℕ) :
    Function.Surjective (coeffsLT (σ := σ) (R := R) N) := by
  classical
  haveI := Fintype.ofFinite (DegLT σ N)
  intro c
  refine ⟨∑ n : DegLT σ N, MvPolynomial.monomial n.1 (c n), ?_⟩
  funext m
  rw [coeffsLT_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro n _ hnm
    rw [MvPolynomial.coeff_monomial, if_neg fun h => hnm (Subtype.ext h)]
  · intro h
    exact absurd (Finset.mem_univ m) h

private def coordAux₁ [Finite σ] (N : ℕ) :=
  LinearMap.quotKerEquivOfSurjective (coeffsLT (σ := σ) (R := R) N) (coeffsLT_surjective N)

private def coordAux₂ (N : ℕ) :=
  Submodule.quotEquivOfEq _ _ (ker_coeffsLT (σ := σ) (R := R) N).symm

private def coordAux₃ (N : ℕ) :=
  (Submodule.Quotient.restrictScalarsEquiv R (truncIdeal σ R N)).symm

private def coordAux₂₁ [Finite σ] (N : ℕ) := (coordAux₂ (σ := σ) (R := R) N) ≪≫ₗ (coordAux₁ N)

variable (σ R) in

def coord [Finite σ] (N : ℕ) : TruncAlg σ R N ≃ₗ[R] (DegLT σ N → R) :=
  (coordAux₃ (σ := σ) (R := R) N) ≪≫ₗ (coordAux₂₁ N)

theorem coord_mk [Finite σ] (N : ℕ) (f : MvPolynomial σ R) (m : DegLT σ N) :
    coord σ R N (Ideal.Quotient.mk (truncIdeal σ R N) f) m = MvPolynomial.coeff m.1 f :=
  rfl

scoped instance instFree [Finite σ] (N : ℕ) : Module.Free R (TruncAlg σ R N) :=
  Module.Free.of_equiv (coord σ R N).symm

scoped instance instFinite [Finite σ] (N : ℕ) : Module.Finite R (TruncAlg σ R N) :=
  Module.Finite.equiv (coord σ R N).symm

variable (R) in

abbrev tX (N : ℕ) (s : σ) : TruncAlg σ R N := Ideal.Quotient.mk _ (MvPolynomial.X s)

theorem mk_eq_mk_iff {N : ℕ} {f g : MvPolynomial σ R} :
    Ideal.Quotient.mk (truncIdeal σ R N) f = Ideal.Quotient.mk _ g ↔
      ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = MvPolynomial.coeff m g := by
  rw [Ideal.Quotient.eq, mem_truncIdeal]
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

theorem monomial_mem_truncIdeal {N : ℕ} {m : σ →₀ ℕ} (hm : N ≤ m.degree) (r : R) :
    MvPolynomial.monomial m r ∈ truncIdeal σ R N := fun n hn => by
  classical
  rw [MvPolynomial.coeff_monomial, if_neg]
  rintro rfl
  exact absurd hm (not_le.2 hn)

theorem prod_tX_pow_eq_zero {N : ℕ} {m : σ →₀ ℕ} (hm : N ≤ m.degree) :
    m.prod (fun s e => (tX R N s) ^ e) = 0 := by
  have h : m.prod (fun s e => (tX R N s) ^ e) =
      Ideal.Quotient.mk _ (m.prod fun s e => (MvPolynomial.X s : MvPolynomial σ R) ^ e) := by
    rw [map_finsuppProd]
    simp only [map_pow]
  rw [h, Finsupp.prod, MvPolynomial.prod_X_pow_eq_monomial, Ideal.Quotient.eq_zero_iff_mem]
  exact monomial_mem_truncIdeal hm 1

theorem isNilpotent_tX (N : ℕ) (s : σ) : IsNilpotent (tX R N s) := by
  refine ⟨N, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.X_pow_eq_monomial]
  exact monomial_mem_truncIdeal (le_of_eq (Finsupp.degree_single _ _).symm) 1

theorem aeval_tX (N : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial.aeval (tX R N) f = Ideal.Quotient.mk (truncIdeal σ R N) f := by
  have h := MvPolynomial.comp_aeval (MvPolynomial.X (R := R) (σ := σ))
    (Ideal.Quotient.mkₐ R (truncIdeal σ R N))
  rw [MvPolynomial.aeval_X_left, AlgHom.comp_id] at h
  exact (DFunLike.congr_fun h f).symm

variable {S : Type*} [CommRing S] [Algebra R S]

theorem aeval_eq_zero_of_mem_truncIdeal {N : ℕ} {w : σ → S}
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0)
    {f : MvPolynomial σ R} (hf : f ∈ truncIdeal σ R N) : MvPolynomial.aeval w f = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m.degree < N
  · rw [hf m hm, map_zero, zero_mul]
  · rw [show (∏ i ∈ m.support, w i ^ m i) = m.prod (fun s e => w s ^ e) from rfl,
      hw m (not_lt.1 hm), mul_zero]

noncomputable def lift (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) :
    TruncAlg σ R N →ₐ[R] S :=
  Ideal.Quotient.liftₐ (truncIdeal σ R N) (MvPolynomial.aeval w)
    (fun _ hf => aeval_eq_zero_of_mem_truncIdeal hw hf)

theorem lift_mk (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) (f : MvPolynomial σ R) :
    lift N w hw (Ideal.Quotient.mk _ f) = MvPolynomial.aeval w f :=
  rfl

theorem lift_tX (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) (s : σ) :
    lift N w hw (tX R N s) = w s := by
  rw [lift_mk, MvPolynomial.aeval_X]

theorem read_linear [Fintype σ] [DecidableEq σ] (c₀ : R) (c : σ → R) (i : σ)
    (h : algebraMap R (TruncAlg σ R 2) c₀ + ∑ j, c j • tX R 2 j = tX R 2 i) :
    c₀ = 0 ∧ ∀ j, c j = if i = j then 1 else 0 := by
  have h0 : Finsupp.degree (0 : σ →₀ ℕ) < 2 := by rw [map_zero]; exact two_pos
  have h1 : ∀ j : σ, (Finsupp.single j 1).degree < 2 := fun j => by
    rw [Finsupp.degree_single]; exact one_lt_two
  have halg : algebraMap R (TruncAlg σ R 2) c₀ = Ideal.Quotient.mk _ (MvPolynomial.C c₀) := rfl
  have key : ∀ m : DegLT σ 2, coord σ R 2 (algebraMap R (TruncAlg σ R 2) c₀ + ∑ j, c j • tX R 2 j) m =
      coord σ R 2 (tX R 2 i) m := fun m => by rw [h]
  simp only [map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, halg, coord_mk] at key
  constructor
  · have k := key ⟨0, h0⟩
    simp only [MvPolynomial.coeff_C, MvPolynomial.coeff_X', if_true] at k
    simpa [Finsupp.single_eq_zero] using k
  · intro j
    have k := key ⟨Finsupp.single j 1, h1 j⟩
    simp only [MvPolynomial.coeff_C, MvPolynomial.coeff_X', Finsupp.single_left_inj one_ne_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at k
    simpa [eq_comm, Ne.symm (Finsupp.single_ne_zero.2 one_ne_zero)] using k

end Trunc

end MvFormalGroup.NaturalLaw
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup"

end
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

noncomputable section

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval hasSubst_elim"
namespace NaturalLaw
p2m_open "MvFormalGroup"

section BotEval

variable {σ : Type*} {R : Type*} [CommRing R]

theorem mem_radical_of_isNilpotent {S : Type*} [CommSemiring S] {I : Ideal S} {x : S}
    (hx : IsNilpotent x) : x ∈ I.radical := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [hn]; exact I.zero_mem⟩

theorem isNilpotent_of_mem_radical_bot {S : Type*} [CommSemiring S] {x : S}
    (hx : x ∈ (⊥ : Ideal S).radical) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, (Ideal.mem_bot).1 hn⟩

theorem isNilpotent_adicEval_bot {S : Type*} [CommRing S] [Algebra R S] [Finite σ] {w : σ → S}
    (hw : ∀ s, IsNilpotent (w s)) {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) :
    IsNilpotent (adicEval ⊥ w F) :=
  isNilpotent_of_mem_radical_bot
    (adicEval_mem_radical ⊥ (fun s => mem_radical_of_isNilpotent (hw s)) hF)

def truncPoly [Finite σ] (N : ℕ) (F : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ n ∈ (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset,
    MvPolynomial.monomial n (MvPowerSeries.coeff n F)

theorem coeff_truncPoly [Finite σ] {N : ℕ} (F : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : m.degree < N) : MvPolynomial.coeff m (truncPoly N F) = MvPowerSeries.coeff m F := by
  classical
  rw [truncPoly, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro n _ hnm
    rw [MvPolynomial.coeff_monomial, if_neg hnm]
  · intro h
    exact absurd ((Set.Finite.mem_toFinset (Finsupp.finite_of_degree_lt N)).2 hm) h

theorem adicEval_bot_tX [Finite σ] (N : ℕ) (F : MvPowerSeries σ R) :
    adicEval ⊥ (tX R N) F = Ideal.Quotient.mk (truncIdeal σ R N) (truncPoly N F) := by
  rw [← aeval_tX]
  exact adicEval_eq_aeval_of_degree ⊥ inferInstance (tX R N) F (truncPoly N F) N
    (fun m hm => prod_tX_pow_eq_zero hm) (fun m hm => coeff_truncPoly F hm)

theorem coord_adicEval_bot_tX [Finite σ] (N : ℕ) (F : MvPowerSeries σ R) (m : DegLT σ N) :
    coord σ R N (adicEval ⊥ (tX R N) F) m = MvPowerSeries.coeff m.1 F := by
  rw [adicEval_bot_tX, coord_mk, coeff_truncPoly F m.2]

theorem eq_of_forall_adicEval_bot_tX_eq [Finite σ] {F G : MvPowerSeries σ R}
    (h : ∀ N : ℕ, adicEval ⊥ (tX R N) F = adicEval ⊥ (tX R N) G) : F = G := by
  ext m
  have := congrArg (fun z => coord σ R (m.degree + 1) z ⟨m, Nat.lt_succ_self _⟩) (h (m.degree + 1))
  simpa only [coord_adicEval_bot_tX] using this

end BotEval
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

end MvFormalGroup.NaturalLaw
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

end
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

noncomputable section

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk coeff_single_inl toPowerSeries coeff_single_inr assoc constantCoeff_eq_zero adicEval adicEval_X adicEval_mem_radical adicEval_subst map_adicEval hasSubst_elim"
namespace NaturalLaw
p2m_open "MvFormalGroup"

section Construction

variable (𝓞 : Type u) [CommRing 𝓞] (d : ℕ)

abbrev testAlg (N : ℕ) : Type u := TruncAlg (Fin d ⊕ Fin d) 𝓞 N

def genX (N : ℕ) : Fin d → testAlg 𝓞 d N := fun j => tX 𝓞 N (Sum.inl j)

def genY (N : ℕ) : Fin d → testAlg 𝓞 d N := fun j => tX 𝓞 N (Sum.inr j)

theorem sumElim_genX_genY (N : ℕ) : Sum.elim (genX 𝓞 d N) (genY 𝓞 d N) = tX 𝓞 N := by
  funext s
  rcases s with j | j <;> rfl

theorem isNilpotent_genX (N : ℕ) (j : Fin d) : IsNilpotent (genX 𝓞 d N j) := isNilpotent_tX N _

theorem isNilpotent_genY (N : ℕ) (j : Fin d) : IsNilpotent (genY 𝓞 d N j) := isNilpotent_tX N _

def transition {N N' : ℕ} (h : N ≤ N') : testAlg 𝓞 d N' →ₐ[𝓞] testAlg 𝓞 d N :=
  lift N' (tX 𝓞 N) (fun _ hm => prod_tX_pow_eq_zero (h.trans hm))

theorem transition_mk {N N' : ℕ} (h : N ≤ N') (f : MvPolynomial (Fin d ⊕ Fin d) 𝓞) :
    transition 𝓞 d h (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f := by
  rw [transition, lift_mk, aeval_tX]

theorem coord_transition {N N' : ℕ} (h : N ≤ N') (z : testAlg 𝓞 d N') (m : Fin d ⊕ Fin d →₀ ℕ)
    (hm : m.degree < N) :
    coord _ 𝓞 N (transition 𝓞 d h z) ⟨m, hm⟩ = coord _ 𝓞 N' z ⟨m, lt_of_lt_of_le hm h⟩ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [transition_mk, coord_mk, coord_mk]

theorem transition_comp_genX {N N' : ℕ} (h : N ≤ N') :
    transition 𝓞 d h ∘ genX 𝓞 d N' = genX 𝓞 d N :=
  funext fun _ => lift_tX _ _ _ _

theorem transition_comp_genY {N N' : ℕ} (h : N ≤ N') :
    transition 𝓞 d h ∘ genY 𝓞 d N' = genY 𝓞 d N :=
  funext fun _ => lift_tX _ _ _ _

variable {𝓞 d}
variable (p : ℕ)
  (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))

def IsNatural : Prop :=
  ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
    [CommRing g'] [Algebra 𝓞 g'] [Module.Free 𝓞 g'] [Module.Finite 𝓞 g']
    (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) →
    (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y

def IsUnital : Prop :=
  ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
    (x : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → μ g x 0 = x ∧ μ g 0 x = x

def IsAssoc : Prop :=
  ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
    (x y z : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) →
    (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, z j ∈ (Ideal.span {(p : g)}).radical) →
    μ g (μ g x y) z = μ g x (μ g y z)

def IsCommut : Prop :=
  ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
    (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) →
    (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g x y = μ g y x

def val (N : ℕ) : Fin d → testAlg 𝓞 d N := μ (testAlg 𝓞 d N) (genX 𝓞 d N) (genY 𝓞 d N)

def series (i : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 := fun m =>
  coord (Fin d ⊕ Fin d) 𝓞 (m.degree + 1) (val μ (m.degree + 1) i) ⟨m, Nat.lt_succ_self _⟩

variable {p μ}

theorem val_eq_transition_comp_val (hnat : IsNatural p μ) {N N' : ℕ} (h : N ≤ N') :
    val μ N = transition 𝓞 d h ∘ val μ N' := by
  have key := hnat (testAlg 𝓞 d N') (testAlg 𝓞 d N) (transition 𝓞 d h) (genX 𝓞 d N') (genY 𝓞 d N')
    (fun j => mem_radical_of_isNilpotent (isNilpotent_genX 𝓞 d N' j))
    (fun j => mem_radical_of_isNilpotent (isNilpotent_genY 𝓞 d N' j))
  rw [transition_comp_genX, transition_comp_genY] at key
  exact key

theorem coeff_series (hnat : IsNatural p μ) {N : ℕ} {m : Fin d ⊕ Fin d →₀ ℕ} (hm : m.degree < N)
    (i : Fin d) : MvPowerSeries.coeff m (series μ i) = coord _ 𝓞 N (val μ N i) ⟨m, hm⟩ := by
  show coord _ 𝓞 (m.degree + 1) (val μ (m.degree + 1) i) ⟨m, _⟩ = _
  rw [val_eq_transition_comp_val hnat (Nat.succ_le_of_lt hm), Function.comp_apply, coord_transition]

theorem adicEval_bot_tX_series (hnat : IsNatural p μ) (N : ℕ) (i : Fin d) :
    adicEval ⊥ (tX 𝓞 N) (series μ i) = val μ N i := by
  apply (coord (Fin d ⊕ Fin d) 𝓞 N).injective
  funext m
  rw [coord_adicEval_bot_tX, coeff_series hnat m.2]
  rfl

theorem adicEval_bot_series (hnat : IsNatural p μ) (g : Type u) [CommRing g] [Algebra 𝓞 g]
    [Module.Free 𝓞 g] [Module.Finite 𝓞 g] {x y : Fin d → g} (hx : ∀ j, IsNilpotent (x j))
    (hy : ∀ j, IsNilpotent (y j)) (i : Fin d) :
    adicEval ⊥ (Sum.elim x y) (series μ i) = μ g x y i := by
  have hxy : ∀ s, IsNilpotent (Sum.elim x y s) := by
    rintro (j | j)
    exacts [hx j, hy j]
  obtain ⟨N, hN⟩ := exists_forall_degree_le_prod_eq_zero_of_isNilpotent (Sum.elim x y) hxy
  let φ : testAlg 𝓞 d N →ₐ[𝓞] g := lift N (Sum.elim x y) hN
  have hφ : ∀ s, φ (tX 𝓞 N s) = Sum.elim x y s := fun s => lift_tX N _ hN s
  have key := hnat (testAlg 𝓞 d N) g φ (genX 𝓞 d N) (genY 𝓞 d N)
    (fun j => mem_radical_of_isNilpotent (isNilpotent_genX 𝓞 d N j))
    (fun j => mem_radical_of_isNilpotent (isNilpotent_genY 𝓞 d N j))
  have hX : φ ∘ genX 𝓞 d N = x := funext fun j => hφ (Sum.inl j)
  have hY : φ ∘ genY 𝓞 d N = y := funext fun j => hφ (Sum.inr j)
  rw [hX, hY] at key
  rw [show μ g x y i = φ (val μ N i) from congrFun key i, ← adicEval_bot_tX_series hnat N i,
    map_adicEval ⊥ ⊥ φ Submodule.fg_bot (fun s hs => ?_)
      (fun s => mem_radical_of_isNilpotent (isNilpotent_tX N s))]
  · exact congrArg (fun w => adicEval ⊥ w (series μ i)) (funext fun s => (hφ s).symm)
  · rw [(Ideal.mem_bot).1 hs, map_zero]
    exact Ideal.zero_mem _

theorem coeff_series_low (hnat : IsNatural p μ) (hunit : IsUnital p μ) (i : Fin d) :
    (series μ i).constantCoeff = 0 ∧
    (∀ j, MvPowerSeries.coeff (Finsupp.single (Sum.inl j) 1) (series μ i) = if i = j then 1 else 0) ∧
    (∀ j, MvPowerSeries.coeff (Finsupp.single (Sum.inr j) 1) (series μ i) = if i = j then 1 else 0) := by
  classical
  have hv : ∀ j, IsNilpotent (tX 𝓞 2 j : TruncAlg (Fin d) 𝓞 2) := fun j => isNilpotent_tX 2 j
  have hv2 : ∀ m : Fin d →₀ ℕ, 2 ≤ m.degree → m.prod (fun t e => (tX 𝓞 2 t : TruncAlg (Fin d) 𝓞 2) ^ e) = 0 :=
    fun m hm => prod_tX_pow_eq_zero hm
  have h0 : ∀ j, IsNilpotent ((0 : Fin d → TruncAlg (Fin d) 𝓞 2) j) := fun _ => IsNilpotent.zero
  obtain ⟨hl, hr⟩ := hunit (TruncAlg (Fin d) 𝓞 2) (tX 𝓞 2) (fun j => mem_radical_of_isNilpotent (hv j))
  have hwl : ∀ s, s ∉ Set.range (Sum.inl : Fin d → Fin d ⊕ Fin d) →
      Sum.elim (tX 𝓞 2) (0 : Fin d → TruncAlg (Fin d) 𝓞 2) s = 0 := by
    rintro (s | s) hs
    · exact absurd ⟨s, rfl⟩ hs
    · rfl
  have hwr : ∀ s, s ∉ Set.range (Sum.inr : Fin d → Fin d ⊕ Fin d) →
      Sum.elim (0 : Fin d → TruncAlg (Fin d) 𝓞 2) (tX 𝓞 2) s = 0 := by
    rintro (s | s) hs
    · rfl
    · exact absurd ⟨s, rfl⟩ hs

  have el := adicEval_bot_series hnat (TruncAlg (Fin d) 𝓞 2) hv h0 i
  rw [hl, adicEval_bot_eq_of_linear Sum.inl Sum.inl_injective (tX 𝓞 2) hv2 (Sum.elim (tX 𝓞 2) 0)
    (fun _ => rfl) hwl] at el
  obtain ⟨hc0, hcl⟩ := read_linear _ _ i el

  have er := adicEval_bot_series hnat (TruncAlg (Fin d) 𝓞 2) h0 hv i
  rw [hr, adicEval_bot_eq_of_linear Sum.inr Sum.inr_injective (tX 𝓞 2) hv2 (Sum.elim 0 (tX 𝓞 2))
    (fun _ => rfl) hwr] at er
  obtain ⟨-, hcr⟩ := read_linear _ _ i er
  refine ⟨?_, hcl, hcr⟩
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hc0

theorem constantCoeff_series (hnat : IsNatural p μ) (hunit : IsUnital p μ) (i : Fin d) :
    (series μ i).constantCoeff = 0 :=
  (coeff_series_low hnat hunit i).1

def law (hnat : IsNatural p μ) (hunit : IsUnital p μ) (hassoc : IsAssoc p μ) : MvFormalGroup d 𝓞 where
  toPowerSeries := series μ
  constantCoeff_eq_zero i := constantCoeff_series hnat hunit i
  coeff_single_inl i j := (coeff_series_low hnat hunit i).2.1 j
  coeff_single_inr i j := (coeff_series_low hnat hunit i).2.2 j
  assoc i := by
    apply eq_of_forall_adicEval_bot_tX_eq (σ := Fin d ⊕ (Fin d ⊕ Fin d)) (R := 𝓞)
    intro N
    have hw : ∀ s, IsNilpotent (tX 𝓞 N s : TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N) :=
      isNilpotent_tX N
    have h0 : ∀ j, (series μ j).constantCoeff = 0 := constantCoeff_series hnat hunit
    rw [adicEval_bot_subst_assoc_left (series μ) h0 hw i,
      adicEval_bot_subst_assoc_right (series μ) h0 hw i]
    have hx : ∀ l, IsNilpotent ((fun l => tX 𝓞 N (Sum.inl l) :
      Fin d → TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N) l) := fun l => hw _
    have hy : ∀ l, IsNilpotent ((fun l => tX 𝓞 N (Sum.inr (Sum.inl l)) :
      Fin d → TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N) l) := fun l => hw _
    have hz : ∀ l, IsNilpotent ((fun l => tX 𝓞 N (Sum.inr (Sum.inr l)) :
      Fin d → TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N) l) := fun l => hw _
    have exy : (fun j => adicEval ⊥ (Sum.elim (fun l => tX 𝓞 N (Sum.inl l))
        fun l => tX 𝓞 N (Sum.inr (Sum.inl l))) (series μ j)) =
        μ (TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N) (fun l => tX 𝓞 N (Sum.inl l))
          fun l => tX 𝓞 N (Sum.inr (Sum.inl l)) :=
      funext fun j => adicEval_bot_series hnat _ hx hy j
    have eyz : (fun j => adicEval ⊥ (Sum.elim (fun l => tX 𝓞 N (Sum.inr (Sum.inl l)))
        fun l => tX 𝓞 N (Sum.inr (Sum.inr l))) (series μ j)) =
        μ (TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N) (fun l => tX 𝓞 N (Sum.inr (Sum.inl l)))
          fun l => tX 𝓞 N (Sum.inr (Sum.inr l)) :=
      funext fun j => adicEval_bot_series hnat _ hy hz j
    have hxy : ∀ j, IsNilpotent (μ (TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N)
        (fun l => tX 𝓞 N (Sum.inl l)) (fun l => tX 𝓞 N (Sum.inr (Sum.inl l))) j) := fun j => by
      rw [← congrFun exy j]
      exact isNilpotent_adicEval_bot (by rintro (l | l) <;> exact hw _) (h0 j)
    have hyz : ∀ j, IsNilpotent (μ (TruncAlg (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 N)
        (fun l => tX 𝓞 N (Sum.inr (Sum.inl l))) (fun l => tX 𝓞 N (Sum.inr (Sum.inr l))) j) :=
      fun j => by
      rw [← congrFun eyz j]
      exact isNilpotent_adicEval_bot (by rintro (l | l) <;> exact hw _) (h0 j)
    rw [exy, eyz, adicEval_bot_series hnat _ hxy hz i, adicEval_bot_series hnat _ hx hyz i]
    exact congrFun (hassoc _ _ _ _ (fun l => mem_radical_of_isNilpotent (hx l))
      (fun l => mem_radical_of_isNilpotent (hy l)) (fun l => mem_radical_of_isNilpotent (hz l))) i

theorem law_toPowerSeries (hnat : IsNatural p μ) (hunit : IsUnital p μ) (hassoc : IsAssoc p μ) :
    (law hnat hunit hassoc).toPowerSeries = series μ :=
  rfl

theorem isComm_law (hnat : IsNatural p μ) (hunit : IsUnital p μ) (hassoc : IsAssoc p μ)
    (hcomm : IsCommut p μ) : (law hnat hunit hassoc).IsComm where
  comm i := by
    rw [law_toPowerSeries]
    apply eq_of_forall_adicEval_bot_tX_eq (σ := Fin d ⊕ Fin d) (R := 𝓞)
    intro N
    have hw : ∀ s, IsNilpotent (tX 𝓞 N s : testAlg 𝓞 d N) := isNilpotent_tX N
    have h0 : ∀ j, (series μ j).constantCoeff = 0 := constantCoeff_series hnat hunit
    rw [adicEval_bot_subst_swap (series μ) hw i]
    have hx := isNilpotent_genX 𝓞 d N
    have hy := isNilpotent_genY 𝓞 d N
    rw [show (Sum.elim (fun j => tX 𝓞 N (Sum.inr j)) fun j => tX 𝓞 N (Sum.inl j)) =
        Sum.elim (genY 𝓞 d N) (genX 𝓞 d N) from rfl,
      adicEval_bot_series hnat _ hy hx i, ← sumElim_genX_genY, adicEval_bot_series hnat _ hx hy i]
    exact congrFun (hcomm _ _ _ (fun j => mem_radical_of_isNilpotent (hy j))
      (fun j => mem_radical_of_isNilpotent (hx j))) i

end Construction
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

theorem existsUnique_law {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ)
    (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
    (hμ_zero : IsUnital p μ) (hμ_assoc : IsAssoc p μ) (hμ_comm : IsCommut p μ)
    (hμ_nat : IsNatural p μ) :
    ∃! Φ : MvFormalGroup d 𝓞, Φ.IsComm ∧
      ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
        (x y : Fin d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
        ∀ i, μ g x y i =
          MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) := by
  refine ⟨law hμ_nat hμ_zero hμ_assoc, ⟨isComm_law hμ_nat hμ_zero hμ_assoc hμ_comm, ?_⟩, ?_⟩
  · intro g _ _ _ _ x y hx hy i
    have hxy : ∀ s, IsNilpotent (Sum.elim x y s) := by
      rintro (j | j)
      exacts [hx j, hy j]
    rw [adicEval_span_natCast_eq_adicEval_bot_of_isNilpotent p hxy, law_toPowerSeries]
    exact (adicEval_bot_series hμ_nat g hx hy i).symm
  · rintro Ψ ⟨-, hΨ⟩
    apply MvFormalGroup.ext
    rw [law_toPowerSeries]
    funext i
    apply eq_of_forall_adicEval_bot_tX_eq (σ := Fin d ⊕ Fin d) (R := 𝓞)
    intro N
    have hx := isNilpotent_genX 𝓞 d N
    have hy := isNilpotent_genY 𝓞 d N
    have hxy : ∀ s, IsNilpotent (Sum.elim (genX 𝓞 d N) (genY 𝓞 d N) s) := by
      rintro (j | j)
      exacts [hx j, hy j]
    have h1 := hΨ (testAlg 𝓞 d N) (genX 𝓞 d N) (genY 𝓞 d N) hx hy i
    rw [adicEval_span_natCast_eq_adicEval_bot_of_isNilpotent p hxy, sumElim_genX_genY] at h1
    have h2 := adicEval_bot_series hμ_nat (testAlg 𝓞 d N) hx hy i
    rw [sumElim_genX_genY] at h2
    exact h1.symm.trans h2.symm

end MvFormalGroup.NaturalLaw
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

end
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural.MvFormalGroup.NaturalLaw"

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ)
    (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
    (hμ_mem : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      ∀ j, μ g x y j ∈ (Ideal.span {(p : g)}).radical)
    (hμ_zero : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → μ g x 0 = x ∧ μ g 0 x = x)
    (hμ_assoc : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y z : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      (∀ j, z j ∈ (Ideal.span {(p : g)}).radical) → μ g (μ g x y) z = μ g x (μ g y z))
    (hμ_comm : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g x y = μ g y x)
    (hμ_nat : ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
      [CommRing g'] [Algebra 𝓞 g'] [Module.Free 𝓞 g'] [Module.Finite 𝓞 g']
      (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y) :
    ∃! Φ : MvFormalGroup d 𝓞, Φ.IsComm ∧
      ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
        (x y : Fin d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
        ∀ i, μ g x y i =
          MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) :=
  MvFormalGroup.NaturalLaw.existsUnique_law p d μ hμ_zero hμ_assoc hμ_comm hμ_nat

end S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
end P2MW
export P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural (solution)
