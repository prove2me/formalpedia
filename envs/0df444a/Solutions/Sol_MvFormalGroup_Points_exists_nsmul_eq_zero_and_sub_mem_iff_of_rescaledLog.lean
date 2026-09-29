-- Prove2me | solution 1 for MvFormalGroup.Points.exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ca581cc3-660f-557c-ad4c-67abc7c6dce4

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_MvPowerSeries_RestrictedEvalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog

set_option autoImplicit false

open MvPowerSeries MvPowerSeries.Restricted

namespace S17L1

section AdicEval

variable {𝓞 : Type*} [CommRing 𝓞] {Y : Type*} [CommRing Y] [Algebra 𝓞 Y] {σ : Type*}

theorem hasEval_of_mem_radical [Finite σ] (J : Ideal Y) {x : σ → Y} (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace Y := J.adicTopology
    MvPowerSeries.HasEval x := by
  letI : TopologicalSpace Y := J.adicTopology
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hx s
    show Filter.Tendsto (x s ^ ·) Filter.atTop (nhds 0)
    rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
    intro n _
    filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
    obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
    rw [pow_add, pow_mul]
    exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))
  · rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

theorem exists_adicEval_sub_psum_mem [Finite σ] (J : Ideal Y) [IsAdicComplete J Y] {x : σ → Y}
    (hx : ∀ s, x s ∈ J.radical) (S : MvPowerSeries σ 𝓞) (N : ℕ) :
    ∃ T₀ : Finset (σ →₀ ℕ), ∀ T : Finset (σ →₀ ℕ), T₀ ⊆ T →
      MvFormalGroup.adicEval J x S - psum x T S ∈ J ^ N := by
  classical
  letI : UniformSpace 𝓞 := ⊥
  letI : WithIdeal Y := ⟨J⟩
  haveI : CompleteSpace Y :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J Y›).1
  haveI : T2Space Y :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J Y›).2
  haveI : ContinuousSMul 𝓞 Y := DiscreteTopology.instContinuousSMul 𝓞 Y
  have ha : MvPowerSeries.HasEval x := hasEval_of_mem_radical J hx
  have heq : MvFormalGroup.adicEval J x S = MvPowerSeries.aeval ha S := by
    rw [← MvFormalGroup.coe_adicEvalAlgHom J hx]
    rfl
  have hsum := MvPowerSeries.hasSum_aeval ha S
  rw [HasSum] at hsum
  have hev := (J.hasBasis_nhds_adic (MvPowerSeries.aeval ha S)).tendsto_right_iff.1 hsum N trivial
  rw [SummationFilter.unconditional_filter, Filter.eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  simp only [Set.mem_image, SetLike.mem_coe] at h
  obtain ⟨z, hz, hzT⟩ := h
  rw [heq]
  have : psum x T S = ∑ d ∈ T, coeff d S • d.prod fun s e => x s ^ e := by
    simp only [psum, monom, Algebra.smul_def]
  rw [this, ← hzT, sub_add_cancel_left]
  exact (J ^ N).neg_mem_iff.2 hz

theorem adicEval_sub_adicEval_mem [Finite σ] (J : Ideal Y) [IsAdicComplete J Y] {x x' : σ → Y}
    (hx : ∀ s, x s ∈ J.radical) (hx' : ∀ s, x' s ∈ J.radical) {N : ℕ} (h : ∀ s, x s - x' s ∈ J ^ N)
    (S : MvPowerSeries σ 𝓞) :
    MvFormalGroup.adicEval J x S - MvFormalGroup.adicEval J x' S ∈ J ^ N := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_adicEval_sub_psum_mem J hx S N
  obtain ⟨T₀', hT₀'⟩ := exists_adicEval_sub_psum_mem J hx' S N
  have h1 := hT₀ (T₀ ∪ T₀') Finset.subset_union_left
  have h2 := hT₀' (T₀ ∪ T₀') Finset.subset_union_right
  have h3 : psum x (T₀ ∪ T₀') S - psum x' (T₀ ∪ T₀') S ∈ J ^ N := by
    rw [psum, psum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [← mul_sub]
    refine Ideal.mul_mem_left _ _ ?_

    simp only [monom, Finsupp.prod]
    have key : ∀ (s : Finset σ), (∏ i ∈ s, x i ^ m i) - (∏ i ∈ s, x' i ^ m i) ∈ J ^ N := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        have : x a ^ m a * ∏ i ∈ s, x i ^ m i - x' a ^ m a * ∏ i ∈ s, x' i ^ m i =
            (x a ^ m a - x' a ^ m a) * ∏ i ∈ s, x i ^ m i +
              x' a ^ m a * (∏ i ∈ s, x i ^ m i - ∏ i ∈ s, x' i ^ m i) := by ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ ih)
        exact (Ideal.Quotient.eq (I := J ^ N)).1 (by
          rw [map_pow, map_pow, (Ideal.Quotient.eq (I := J ^ N)).2 (h a)])
    exact key _
  have : MvFormalGroup.adicEval J x S - MvFormalGroup.adicEval J x' S =
      (MvFormalGroup.adicEval J x S - psum x (T₀ ∪ T₀') S) +
        (psum x (T₀ ∪ T₀') S - psum x' (T₀ ∪ T₀') S) -
          (MvFormalGroup.adicEval J x' S - psum x' (T₀ ∪ T₀') S) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.add_mem _ h1 h3) h2

omit [Algebra 𝓞 Y] in
theorem monom_smul (c : Y) (t : σ → Y) (m : σ →₀ ℕ) :
    monom (fun s => c * t s) m = c ^ m.degree * monom t m := by
  classical
  simp only [monom, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  simp

theorem tendsto0_of_rescale [Finite σ] {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {S Sp : MvPowerSeries σ 𝓞}
    (hSp : ∀ m : σ →₀ ℕ, m ≠ 0 → coeff m Sp * (p : 𝓞) = (p : 𝓞) ^ m.degree * coeff m S) :
    Tendsto0 p Sp := by
  classical
  apply Tendsto0.of_degree
  intro N
  refine ⟨N + 1, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have h := hSp m hm0
  obtain ⟨k, hk⟩ : ∃ k, m.degree = N + 1 + k := ⟨m.degree - (N + 1), by omega⟩
  rw [hk, pow_add, pow_add, pow_one, mul_assoc, mul_assoc, mul_comm ((p : 𝓞))
    ((p : 𝓞) ^ k * coeff m S), ← mul_assoc] at h
  have h' := (mul_cancel_right_mem_nonZeroDivisors hp).1 h
  rw [h']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem adicEval_smul_eq_mul_evalT [Finite σ] {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hY : Cplt p Y) {S Sp : MvPowerSeries σ 𝓞}
    (hSp : ∀ m : σ →₀ ℕ, m ≠ 0 → coeff m Sp * (p : 𝓞) = (p : 𝓞) ^ m.degree * coeff m S)
    (hS0 : constantCoeff S = 0) (hSp0 : constantCoeff Sp = 0) (t : σ → Y) :
    MvFormalGroup.adicEval (Ideal.span {(p : Y)}) (fun s => (p : Y) * t s) S =
      (p : Y) * evalT p hY t Sp := by
  classical
  haveI : IsAdicComplete (Ideal.span {(p : Y)}) Y := hY
  have hx : ∀ s, (p : Y) * t s ∈ (Ideal.span {(p : Y)}).radical :=
    fun s => Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hT0 := tendsto0_of_rescale hp hSp
  refine eq_of_forall_sub_mem p hY fun N => ?_
  obtain ⟨T₀, hT₀⟩ := exists_adicEval_sub_psum_mem (Ideal.span {(p : Y)}) hx S N
  set T := T₀ ∪ hT0.bad N
  have h1 := hT₀ T Finset.subset_union_left
  rw [Ideal.span_singleton_pow] at h1
  have h2 := evalT_sub_psum_mem p hY hT0 t (N := N) (T := T) Finset.subset_union_right
  have h3 : psum (fun s => (p : Y) * t s) T S = (p : Y) * psum t T Sp := by
    rw [psum, psum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm0 : m = 0
    · subst hm0
      have e1 : coeff (0 : σ →₀ ℕ) S = 0 := by rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hS0; exact hS0
      have e2 : coeff (0 : σ →₀ ℕ) Sp = 0 := by rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hSp0; exact hSp0
      simp [e1, e2]
    · rw [monom_smul, ← mul_assoc, mul_comm (algebraMap 𝓞 Y (coeff m S)), ← map_natCast (algebraMap 𝓞 Y),
        ← map_pow, ← map_mul, ← hSp m hm0, map_mul, map_natCast]
      ring
  have : MvFormalGroup.adicEval (Ideal.span {(p : Y)}) (fun s => (p : Y) * t s) S - (p : Y) * evalT p hY t Sp =
      (MvFormalGroup.adicEval (Ideal.span {(p : Y)}) (fun s => (p : Y) * t s) S - psum (fun s => (p : Y) * t s) T S)
        - (p : Y) * (evalT p hY t Sp - psum t T Sp) := by rw [h3]; ring
  rw [this]
  exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ h2)

end AdicEval

section Iso

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
  (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
  (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
  (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
  (hψT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
  (hφF : ∀ i, subst Fp (φ i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
  (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
  {Y : Type*} [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
  (hY : Cplt p Y)

local notation "J" => Ideal.span {((p : ℕ) : Y)}

noncomputable def Phi (t : Fin d → Y) : Fin d → Y := fun i => evalT p hY t (φ i)
noncomputable def Psi (u : Fin d → Y) : Fin d → Y := fun i => evalT p hY u (ψ i)

omit [Fact p.Prime] in
include hφT in
theorem tφ (i : Fin d) : Tendsto0 p (φ i) := fun N => hφT N i
omit [Fact p.Prime] in
include hψT in
theorem tψ (i : Fin d) : Tendsto0 p (ψ i) := fun N => hψT N i

include hφT hψT hφψ hψ0 in
theorem Phi_Psi (u : Fin d → Y) : Phi p φ hY (Psi p ψ hY u) = u := by
  funext i
  show evalT p hY (fun j => evalT p hY u (ψ j)) (φ i) = u i
  rw [← evalT_subst p hY hψ0 (tψ p ψ hψT) (tφ p φ hφT i), hφψ, evalT_X]

include hφT hψT hψφ hφ0 in
theorem Psi_Phi (t : Fin d → Y) : Psi p ψ hY (Phi p φ hY t) = t := by
  funext i
  show evalT p hY (fun j => evalT p hY t (φ j)) (ψ i) = t i
  rw [← evalT_subst p hY hφ0 (tφ p φ hφT) (tψ p ψ hψT i), hψφ, evalT_X]

noncomputable def ptOf (u : Fin d → Y) : MvFormalGroup.Points F Y J :=
  ⟨fun i => (p : Y) * Psi p ψ hY u i,
    fun i => Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))⟩

@[scoped simp] theorem val_ptOf (u : Fin d → Y) (i : Fin d) : (ptOf p F ψ hY u).val i = (p : Y) * Psi p ψ hY u i :=
  rfl

include hp in

theorem eq_zero_of_p_mul_eq_zero {a : Y} (h : (p : Y) * a = 0) : a = 0 := by
  classical
  let b := Module.Free.chooseBasis 𝓞 Y
  have hrepr : ∀ i, b.repr a i = 0 := by
    intro i
    have h1 : b.repr ((p : Y) * a) i = 0 := by rw [h, map_zero, Finsupp.zero_apply]
    have h2 : (p : Y) * a = (p : 𝓞) • a := by
      rw [Algebra.smul_def, map_natCast]
    rw [h2, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact (mem_nonZeroDivisors_iff.mp hp).1 _ h1
  have : b.repr a = 0 := Finsupp.ext hrepr
  exact b.repr.map_eq_zero_iff.1 this

include hp in
theorem eq_of_p_mul_eq {a b : Y} (h : (p : Y) * a = (p : Y) * b) : a = b := by
  rw [← sub_eq_zero] at h ⊢
  rw [← mul_sub] at h
  exact eq_zero_of_p_mul_eq_zero p hp h

omit [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] in

theorem exists_eq_p_mul {a : Y} (ha : a ∈ J) : ∃ t : Y, a = (p : Y) * t := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ha
  exact ⟨t, by rw [← ht, mul_comm]⟩

include hp hFp in
theorem tendsto0_Fp (i : Fin d) : Tendsto0 p (Fp i) :=
  tendsto0_of_rescale hp (hFp i)

include hp hFp hFp0 in

theorem val_ptOf_add (u₁ u₂ : Fin d → Y) (i : Fin d) :
    (haveI : IsAdicComplete J Y := hY; (ptOf p F ψ hY u₁ + ptOf p F ψ hY u₂).val i) =
      (p : Y) * evalT p hY (Sum.elim (Psi p ψ hY u₁) (Psi p ψ hY u₂)) (Fp i) := by
  haveI : IsAdicComplete J Y := hY
  show (ptOf p F ψ hY u₁ + ptOf p F ψ hY u₂).val i = _
  rw [MvFormalGroup.Points.val_add]
  have hx : Sum.elim (ptOf p F ψ hY u₁).val (ptOf p F ψ hY u₂).val =
      fun s => (p : Y) * Sum.elim (Psi p ψ hY u₁) (Psi p ψ hY u₂) s := by
    funext s; rcases s with j | j <;> rfl
  rw [hx]
  exact adicEval_smul_eq_mul_evalT hp hY (hFp i) (F.constantCoeff_eq_zero i) (hFp0 i) _

omit [Fact p.Prime] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] in
theorem evalT_subst_X_inl (t : Fin d ⊕ Fin d → Y) {S : MvPowerSeries (Fin d) 𝓞} (hS : Tendsto0 p S) :
    evalT p hY t (subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) S) =
      evalT p hY (fun j => t (Sum.inl j)) S := by
  rw [evalT_subst p hY (fun j => constantCoeff_X _) (fun j => tendsto0_X p _) hS]
  congr 1
  funext j
  exact evalT_X p hY t _

omit [Fact p.Prime] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] in
theorem evalT_subst_X_inr (t : Fin d ⊕ Fin d → Y) {S : MvPowerSeries (Fin d) 𝓞} (hS : Tendsto0 p S) :
    evalT p hY t (subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) S) =
      evalT p hY (fun j => t (Sum.inr j)) S := by
  rw [evalT_subst p hY (fun j => constantCoeff_X _) (fun j => tendsto0_X p _) hS]
  congr 1
  funext j
  exact evalT_X p hY t _

include hp hFp hφT hψT hφψ hψ0 hφF hFp0 in

theorem Phi_evalT_Fp (u₁ u₂ : Fin d → Y) :
    Phi p φ hY (fun i => evalT p hY (Sum.elim (Psi p ψ hY u₁) (Psi p ψ hY u₂)) (Fp i)) = u₁ + u₂ := by
  have hFpT : ∀ j, Tendsto0 p (Fp j) := tendsto0_Fp p hp F Fp hFp
  funext i
  simp only [Phi, Pi.add_apply]
  rw [← evalT_subst p hY hFp0 hFpT (tφ p φ hφT i), hφF,
    evalT_add p hY (tendsto0_subst p (fun j => constantCoeff_X _) (fun j => tendsto0_X p _) (tφ p φ hφT i))
      (tendsto0_subst p (fun j => constantCoeff_X _) (fun j => tendsto0_X p _) (tφ p φ hφT i)),
    evalT_subst_X_inl p hY _ (tφ p φ hφT i), evalT_subst_X_inr p hY _ (tφ p φ hφT i)]
  have h1 := congrFun (Phi_Psi p φ ψ hψ0 hφT hψT hφψ hY u₁) i
  have h2 := congrFun (Phi_Psi p φ ψ hψ0 hφT hψT hφψ hY u₂) i
  simp only [Phi] at h1 h2
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h1, h2]

include hp hFp hφT hψT hφψ hψφ hψ0 hφ0 hφF hFp0 in

theorem ptOf_add (u₁ u₂ : Fin d → Y) :
    (haveI : IsAdicComplete J Y := hY; ptOf p F ψ hY u₁ + ptOf p F ψ hY u₂) = ptOf p F ψ hY (u₁ + u₂) := by
  haveI : IsAdicComplete J Y := hY
  show ptOf p F ψ hY u₁ + ptOf p F ψ hY u₂ = ptOf p F ψ hY (u₁ + u₂)
  apply MvFormalGroup.Points.ext
  funext i
  rw [val_ptOf_add p hp F Fp hFp hFp0, val_ptOf]
  congr 1
  have key : (fun i => evalT p hY (Sum.elim (Psi p ψ hY u₁) (Psi p ψ hY u₂)) (Fp i)) = Psi p ψ hY (u₁ + u₂) := by
    have h := Phi_evalT_Fp p hp F Fp hFp hFp0 φ ψ hψ0 hφT hψT hφF hφψ hY u₁ u₂
    have h' := congrArg (Psi p ψ hY) h
    rwa [Psi_Phi p φ ψ hφ0 hφT hψT hψφ hY] at h'
  exact congrFun key i

noncomputable def ptOfHom : (Fin d → Y) →+ (haveI : IsAdicComplete J Y := hY; MvFormalGroup.Points F Y J) :=
  haveI : IsAdicComplete J Y := hY
  { toFun := ptOf p F ψ hY
    map_zero' := by
      have h := ptOf_add p hp F Fp hFp hFp0 φ ψ hφ0 hψ0 hφT hψT hφF hψφ hφψ hY 0 0
      rw [add_zero] at h
      exact add_left_cancel (h.trans (add_zero _).symm)
    map_add' := fun u₁ u₂ => (ptOf_add p hp F Fp hFp hFp0 φ ψ hφ0 hψ0 hφT hψT hφF hψφ hφψ hY u₁ u₂).symm }

end Iso

section Main

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
  (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
  (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
  (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
  (hψT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
  (hφF : ∀ i, subst Fp (φ i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
  (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
  {Y : Type*} [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
  [hYi : IsAdicComplete (Ideal.span {((p : ℕ) : Y)}) Y]

local notation "J" => Ideal.span {((p : ℕ) : Y)}

include hφT hψT hψφ hφ0 in

theorem eq_ptOf_Phi (z : MvFormalGroup.Points F Y J) (t : Fin d → Y) (hz : ∀ i, z.val i = (p : Y) * t i) :
    z = ptOf p F ψ hYi (Phi p φ hYi t) := by
  apply MvFormalGroup.Points.ext
  funext i
  rw [val_ptOf, Psi_Phi p φ ψ hφ0 hφT hψT hψφ hYi, hz]

include hp hφT hψT hφψ hψ0 in
theorem ptOf_injective : Function.Injective (ptOf p F ψ hYi) := by
  intro a b hab
  have h : Psi p ψ hYi a = Psi p ψ hYi b := by
    funext i
    have := congrFun (congrArg MvFormalGroup.Points.val hab) i
    rw [val_ptOf, val_ptOf] at this
    exact eq_of_p_mul_eq p hp this
  have h' := congrArg (Phi p φ hYi) h
  rwa [Phi_Psi p φ ψ hψ0 hφT hψT hφψ hYi, Phi_Psi p φ ψ hψ0 hφT hψT hφψ hYi] at h'

omit [Fact p.Prime] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] [F.IsComm] in
omit [Fact p.Prime] in
theorem mem_of_mem_pow_one {I : Ideal Y} {a : Y} (h : a ∈ I ^ 1) : a ∈ I := by
  rwa [pow_one] at h

omit [Fact p.Prime] in

theorem forall_sumElim {α β M : Type*} {q : M → Prop} {x : α → M} {y : β → M}
    (hx : ∀ a, q (x a)) (hy : ∀ b, q (y b)) : ∀ c, q (Sum.elim x y c) := by
  rintro (a | b)
  exacts [hx a, hy b]

theorem val_add_sub_val_mem (a e : MvFormalGroup.Points F Y J) (he : ∀ i, e.val i ∈ J) (i : Fin d) :
    (a + e).val i - a.val i ∈ J := by
  have h0 : a.val i = (a + 0).val i := by rw [add_zero]
  rw [h0, MvFormalGroup.Points.val_add, MvFormalGroup.Points.val_add]
  refine mem_of_mem_pow_one (adicEval_sub_adicEval_mem _ ?_ ?_ ?_ _)
  · exact forall_sumElim a.mem_radical e.mem_radical
  · exact forall_sumElim a.mem_radical (0 : MvFormalGroup.Points F Y J).mem_radical
  · rintro (j | j)
    · simp
    · simp only [Sum.elim_inr, MvFormalGroup.Points.val_zero, sub_zero, pow_one]; exact he j

omit [Fact p.Prime] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] [F.IsComm] in

theorem val_neg_sub_val_neg_mem (a b : MvFormalGroup.Points F Y J) (h : ∀ i, a.val i - b.val i ∈ J) (i : Fin d) :
    (-a).val i - (-b).val i ∈ J := by
  rw [MvFormalGroup.Points.val_neg, MvFormalGroup.Points.val_neg]
  refine mem_of_mem_pow_one (adicEval_sub_adicEval_mem _ a.mem_radical b.mem_radical ?_ _)
  intro j; rw [pow_one]; exact h j

omit [Fact p.Prime] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] [F.IsComm] in

theorem val_sub_mem (a b : MvFormalGroup.Points F Y J) (h : ∀ i, b.val i - a.val i ∈ J) (i : Fin d) :
    (a - b).val i ∈ J := by
  have h1 : (a + (-b)).val i - (a + (-a)).val i ∈ J := by
    rw [MvFormalGroup.Points.val_add, MvFormalGroup.Points.val_add]
    refine mem_of_mem_pow_one (adicEval_sub_adicEval_mem _ ?_ ?_ ?_ _)
    · exact forall_sumElim a.mem_radical (-b).mem_radical
    · exact forall_sumElim a.mem_radical (-a).mem_radical
    · rintro (j | j)
      · simp
      · simp only [Sum.elim_inr, pow_one]; exact val_neg_sub_val_neg_mem p F b a h j
  rwa [add_neg_cancel, MvFormalGroup.Points.val_zero, sub_zero, ← sub_eq_add_neg] at h1

noncomputable def box (d n : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finset.univ : Finset (Fin d → Fin n)).image fun f => Finsupp.equivFunOnFinite.symm fun j => (f j : ℕ)

omit [Fact p.Prime] in
theorem mem_box {d n : ℕ} (m : Fin d →₀ ℕ) : m ∈ box d n ↔ ∀ j, m j < n := by
  constructor
  · intro hm j
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hm
    simp
  · intro h
    refine Finset.mem_image.2 ⟨fun j => ⟨m j, h j⟩, Finset.mem_univ _, ?_⟩
    ext j; simp

omit [Fact p.Prime] in
theorem exists_subset_box {d : ℕ} (T : Finset (Fin d →₀ ℕ)) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → T ⊆ box d n := by
  classical
  refine ⟨T.sup (fun m => (Finset.univ : Finset (Fin d)).sup m) + 1, fun n hn m hm => ?_⟩
  rw [mem_box]
  intro j
  have h1 : m j ≤ (Finset.univ : Finset (Fin d)).sup m := Finset.le_sup (f := m) (Finset.mem_univ j)
  have h2 : (Finset.univ : Finset (Fin d)).sup m ≤ T.sup fun m => (Finset.univ : Finset (Fin d)).sup m :=
    Finset.le_sup (f := fun m : Fin d →₀ ℕ => (Finset.univ : Finset (Fin d)).sup m) hm
  omega

omit [Fact p.Prime] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] hYi in

theorem aeval_eq_psum_box {n : ℕ} {S : MvPowerSeries (Fin d) 𝓞} (P : MvPolynomial (Fin d) 𝓞)
    (hP : ∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then coeff m S else 0) (w' : Fin d → Y) :
    MvPolynomial.aeval w' P = psum w' (box d n) S := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, psum]
  have hsupp : P.support ⊆ box d n := by
    intro m hm
    rw [mem_box]
    by_contra h
    rw [MvPolynomial.mem_support_iff, hP, if_neg h] at hm
    exact hm rfl
  rw [← Finset.sum_subset hsupp]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [hP, if_pos ((mem_box m).1 (hsupp hm)), monom, Finsupp.prod]
  · intro m hmb hm
    have h0 := hP m
    rw [MvPolynomial.notMem_support_iff.1 hm, if_pos ((mem_box m).1 hmb)] at h0
    rw [← h0, map_zero, zero_mul]

omit [Fact p.Prime] in

theorem exists_box_poly (n : ℕ) (S : MvPowerSeries (Fin d) 𝓞) :
    ∃ P : MvPolynomial (Fin d) 𝓞, ∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then coeff m S else 0 := by
  classical
  refine ⟨∑ m ∈ box d n, MvPolynomial.monomial m (coeff m S), fun m => ?_⟩
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [mem_box]

include hp in
theorem eq_zero_of_pow_mul_eq_zero : ∀ (k : ℕ) {a : Y}, (p : Y) ^ k * a = 0 → a = 0
  | 0, a, h => by simpa using h
  | k + 1, a, h => by
    rw [pow_succ, mul_assoc] at h
    exact eq_zero_of_p_mul_eq_zero p hp (eq_zero_of_pow_mul_eq_zero k h)

omit [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y] in
theorem eq_zero_of_coprime_mul_eq_zero {m : ℕ} (hm : ¬ p ∣ m) {a : Y} (h : (m : Y) * a = 0) : a = 0 := by
  refine eq_of_forall_sub_mem p hYi fun N => ?_
  rw [sub_zero]
  have hcop : Nat.Coprime (p ^ N) m := (Nat.Coprime.pow_left N ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
  obtain ⟨u, v, huv⟩ : IsCoprime ((p : ℤ) ^ N) (m : ℤ) := by
    have := Nat.isCoprime_iff_coprime.2 hcop
    simpa using this
  have h1 : (u : Y) * (p : Y) ^ N + (v : Y) * (m : Y) = 1 := by
    have := congrArg (Int.cast : ℤ → Y) huv
    simpa using this
  have : a = (p : Y) ^ N * ((u : Y) * a) := by
    calc a = ((u : Y) * (p : Y) ^ N + (v : Y) * (m : Y)) * a := by rw [h1, one_mul]
      _ = (p : Y) ^ N * ((u : Y) * a) + (v : Y) * ((m : Y) * a) := by ring
      _ = (p : Y) ^ N * ((u : Y) * a) := by rw [h, mul_zero, add_zero]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

include hp in
theorem eq_zero_of_natCast_mul_eq_zero {n : ℕ} (hn : n ≠ 0) {a : Y} (h : (n : Y) * a = 0) : a = 0 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Nat.Prime.ne_one Fact.out)
  rw [Nat.cast_mul, Nat.cast_pow, mul_assoc] at h
  exact eq_zero_of_coprime_mul_eq_zero p hm (eq_zero_of_pow_mul_eq_zero p hp k h)

include hp hFp hFp0 hφ0 hψ0 hφT hψT hφF hψφ hφψ in
theorem mainA (y : MvFormalGroup.Points F Y J) (v : ℕ) (w' : Fin d → Y)
    (hw' : ∀ i, (p ^ v • y).val i = (p : Y) * w' i) :
    (∃ y' : MvFormalGroup.Points F Y J, p ^ v • y' = 0 ∧ ∀ i, y'.val i - y.val i ∈ J) ↔
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
          MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} := by
  classical
  have hyv : p ^ v • y = ptOf p F ψ hYi (Phi p φ hYi w') := eq_ptOf_Phi p F φ ψ hφ0 hφT hψT hψφ (p ^ v • y) w' hw'
  let H := ptOfHom p hp F Fp hFp hFp0 φ ψ hφ0 hψ0 hφT hψT hφF hψφ hφψ hYi
  have hH : ∀ u, H u = ptOf p F ψ hYi u := fun u => rfl

  obtain ⟨n₁, hn₁⟩ := exists_subset_box ((Finset.univ : Finset (Fin d)).biUnion fun i => (tφ p φ hφT i).bad v)
  have hbad : ∀ n, n₁ ≤ n → ∀ i, (tφ p φ hφT i).bad v ⊆ box d n := fun n hn i =>
    (Finset.subset_biUnion_of_mem (fun i => (tφ p φ hφT i).bad v) (Finset.mem_univ i)).trans (hn₁ n hn)

  have key : (∀ i, Phi p φ hYi w' i ∈ Ideal.span {(p : Y) ^ v}) ↔
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
          MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} := by
    constructor
    · intro hΦ
      refine ⟨n₁, fun n hn i P hP => ?_⟩
      rw [aeval_eq_psum_box P hP w']
      have h1 := evalT_sub_psum_mem p hYi (tφ p φ hφT i) w' (hbad n hn i)
      have h2 := hΦ i
      simp only [Phi] at h2
      have := Ideal.sub_mem _ h2 h1
      rwa [sub_sub_cancel] at this
    · rintro ⟨n₀, hn₀⟩ i
      obtain ⟨P, hP⟩ := exists_box_poly (max n₀ n₁) (φ i)
      have h1 := hn₀ (max n₀ n₁) (le_max_left _ _) i P hP
      rw [aeval_eq_psum_box P hP w'] at h1
      have h2 := evalT_sub_psum_mem p hYi (tφ p φ hφT i) w' (hbad (max n₀ n₁) (le_max_right _ _) i)
      have := Ideal.add_mem _ h2 h1
      rwa [sub_add_cancel] at this
  rw [← key]
  constructor
  ·
    rintro ⟨y', hy'0, hy'⟩
    set e := y - y'
    have he : ∀ i, e.val i ∈ J := val_sub_mem p F y y' hy'
    choose t ht using fun i => exists_eq_p_mul p (he i)
    have he' : e = ptOf p F ψ hYi (Phi p φ hYi t) := eq_ptOf_Phi p F φ ψ hφ0 hφT hψT hψφ e t ht
    have h1 : p ^ v • e = ptOf p F ψ hYi (Phi p φ hYi w') := by
      rw [← hyv]; simp only [e, nsmul_sub, hy'0, sub_zero]
    have h2 : p ^ v • e = ptOf p F ψ hYi (p ^ v • Phi p φ hYi t) := by
      rw [he', ← hH, ← map_nsmul, hH]
    have h3 : Phi p φ hYi w' = p ^ v • Phi p φ hYi t :=
      ptOf_injective p hp F φ ψ hψ0 hφT hψT hφψ (h1.symm.trans h2)
    intro i
    rw [h3, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  ·
    intro hΦ
    choose u hu using fun i => Ideal.mem_span_singleton'.1 (hΦ i)

    have hΦu : Phi p φ hYi w' = p ^ v • u := by
      funext i; rw [Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, ← hu i, mul_comm]
    refine ⟨y - H u, ?_, ?_⟩
    · rw [nsmul_sub, hyv, ← map_nsmul, hH, ← hΦu, sub_self]
    · intro i
      rw [show y - H u = y + H (-u) by rw [map_neg, sub_eq_add_neg], hH]
      exact val_add_sub_val_mem p F y _ (fun j => Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) i

include hp hφ0 hψ0 hφT hψT hφF hψφ hφψ hFp hFp0 in
theorem mainB (z : MvFormalGroup.Points F Y J) (hz : ∀ i, z.val i ∈ J) (n : ℕ) (hn : n ≠ 0) :
    n • z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, nsmul_zero]⟩
  choose t ht using fun i => exists_eq_p_mul p (hz i)
  have hz' : z = ptOf p F ψ hYi (Phi p φ hYi t) := eq_ptOf_Phi p F φ ψ hφ0 hφT hψT hψφ z t ht
  let H := ptOfHom p hp F Fp hFp hFp0 φ ψ hφ0 hψ0 hφT hψT hφF hψφ hφψ hYi
  have hH : ∀ u, H u = ptOf p F ψ hYi u := fun u => rfl
  have h1 : ptOf p F ψ hYi (n • Phi p φ hYi t) = ptOf p F ψ hYi 0 := by
    rw [← hH, map_nsmul, hH, ← hz', h, ← hH, map_zero]
  have h2 := ptOf_injective p hp F φ ψ hψ0 hφT hψT hφψ h1
  have h3 : Phi p φ hYi t = 0 := by
    funext i
    have := congrFun h2 i
    rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at this
    exact eq_zero_of_natCast_mul_eq_zero p hp hn this
  rw [hz', h3, ← hH, map_zero]

end Main

end S17L1
p2m_reactivate "P2MW.S_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog.S17L1"

set_option autoImplicit false

open MvPowerSeries

universe u w

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hψT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    [IsAdicComplete (Ideal.span {(p : Y)}) Y]
    (y : MvFormalGroup.Points F Y (Ideal.span {(p : Y)})) (v : ℕ)
    (w' : Fin d → Y) (hw' : ∀ i, (p ^ v • y).val i = (p : Y) * w' i) :
    (∃ y' : MvFormalGroup.Points F Y (Ideal.span {(p : Y)}),
        p ^ v • y' = 0 ∧ ∀ i, y'.val i - y.val i ∈ Ideal.span {(p : Y)}) ↔
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
          MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} :=
  S17L1.mainA (p := p) (hp := hp) (F := F) (Fp := Fp) (hFp := hFp) (hFp0 := hFp0) (φ := φ) (ψ := ψ) (hφ0 := hφ0) (hψ0 := hψ0)
    (hφT := hφT) (hψT := hψT) (hφF := hφF) (hψφ := hψφ) (hφψ := hφψ) (y := y) (v := v) (w' := w') (hw' := hw')

end S_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog
end P2MW
export P2MW.S_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog (solution)
