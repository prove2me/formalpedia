-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isTwistType_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f932983f-0df1-5971-8af0-00917ecc1098

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_ModularCurve_JHTwistedDatum
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistPosMoment_eq_one_of_inertiaStable_of_annulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isTwistType_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_annulus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

noncomputable section

namespace SndTT

open Classical

section Lattice
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eq_const_of_forall_sum_mul_eq_zero (β : ι → ℤ)
    (h : ∀ c : characterLattice ι, ∑ s, β s * c.1 s = 0) : ∀ s s', β s = β s' := by
  intro s s'
  by_cases hss : s = s'
  · rw [hss]
  have hmem : (Pi.single s (1 : ℤ) - Pi.single s' 1) ∈ characterLattice ι := by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]
  have h1 := h ⟨_, hmem⟩
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h1
  have e1 : ∑ x, β x * Pi.single (M := fun _ => ℤ) s (1 : ℤ) x = β s := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hs; exact absurd (Finset.mem_univ s) hs
  have e2 : ∑ x, β x * Pi.single (M := fun _ => ℤ) s' (1 : ℤ) x = β s' := by
    rw [Finset.sum_eq_single s']
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hs; exact absurd (Finset.mem_univ s') hs
  rw [e1, e2] at h1
  linarith

theorem exists_coeff_of_mem_range_gramMap (e : ι → ℕ) (α : ι → ℤ)
    (h : (∑ s, α s • crossingCoord s : Module.Dual ℤ (characterLattice ι)) ∈ LinearMap.range (gramMap e)) :
    ∃ (γ : ι → ℤ) (κ : ℤ), (∑ s, γ s = 0) ∧ ∀ s, α s = (e s : ℤ) * γ s + κ := by
  obtain ⟨γΛ, hγ⟩ := h
  have hΛ : ∑ s, γΛ.1 s = 0 := mem_characterLattice.mp γΛ.2

  have hkill : ∀ c : characterLattice ι, ∑ s, (α s - (e s : ℤ) * γΛ.1 s) * c.1 s = 0 := by
    intro c
    have h1 := LinearMap.congr_fun hγ c
    rw [gramMap_apply, LinearMap.sum_apply] at h1
    simp only [LinearMap.smul_apply, crossingCoord_apply, smul_eq_mul] at h1
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← h1]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hconst := eq_const_of_forall_sum_mul_eq_zero _ hkill
  by_cases hι : Nonempty ι
  · obtain ⟨s₁⟩ := hι
    refine ⟨γΛ.1, α s₁ - (e s₁ : ℤ) * γΛ.1 s₁, hΛ, fun s => ?_⟩
    have := hconst s s₁
    linarith
  · refine ⟨γΛ.1, 0, hΛ, fun s => ?_⟩
    exact absurd ⟨s⟩ hι

end Lattice

noncomputable def tent (t : ℚ) (d : ℕ) : ℚ := max 0 (1 - |t - d|)

theorem tent_eq (t : ℚ) (h0 : 0 ≤ t) (d : ℕ) :
    tent t d = if d = ⌊t⌋₊ then 1 - (t - ⌊t⌋₊) else if d = ⌊t⌋₊ + 1 then t - ⌊t⌋₊ else 0 := by
  have hfl : (⌊t⌋₊ : ℚ) ≤ t := Nat.floor_le h0
  have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  unfold tent
  by_cases h1 : d = ⌊t⌋₊
  · subst h1
    rw [if_pos rfl, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  · rw [if_neg h1]
    by_cases h2 : d = ⌊t⌋₊ + 1
    · subst h2
      rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith), max_eq_right (by push_cast; linarith)]
      push_cast; ring
    · rw [if_neg h2]
      apply max_eq_left

      rcases lt_or_gt_of_ne h1 with hlt' | hgt'
      ·
        have : (d : ℚ) + 1 ≤ ⌊t⌋₊ := by exact_mod_cast hlt'
        rw [abs_of_nonneg (by linarith)]
        linarith
      ·
        have hd2 : ⌊t⌋₊ + 2 ≤ d := by omega
        have : (⌊t⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast hd2
        rw [abs_of_nonpos (by linarith)]
        linarith

theorem tent_sum_eq_one {L : ℕ} {t : ℚ} (h0 : 0 < t) (hL : t < L) :
    ∑ d ∈ Finset.range (L + 1), tent t d = 1 := by
  have hfl : (⌊t⌋₊ : ℚ) ≤ t := Nat.floor_le h0.le
  have hn : ⌊t⌋₊ + 1 ≤ L := by
    have : ⌊t⌋₊ < L := by
      by_contra h
      push_neg at h
      have : (L : ℚ) ≤ ⌊t⌋₊ := by exact_mod_cast h
      linarith
    omega
  have hsub : ({⌊t⌋₊, ⌊t⌋₊ + 1} : Finset ℕ) ⊆ Finset.range (L + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega), tent_eq t h0.le, tent_eq t h0.le, if_pos rfl, if_neg (by omega), if_pos rfl]
    ring
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [tent_eq t h0.le, if_neg hx.1, if_neg hx.2]

theorem tent_sum_mul_eq {L : ℕ} {t : ℚ} (h0 : 0 < t) (hL : t < L) :
    ∑ d ∈ Finset.range (L + 1), (d : ℚ) * tent t d = t := by
  have hfl : (⌊t⌋₊ : ℚ) ≤ t := Nat.floor_le h0.le
  have hn : ⌊t⌋₊ + 1 ≤ L := by
    have : ⌊t⌋₊ < L := by
      by_contra h
      push_neg at h
      have : (L : ℚ) ≤ ⌊t⌋₊ := by exact_mod_cast h
      linarith
    omega
  have hsub : ({⌊t⌋₊, ⌊t⌋₊ + 1} : Finset ℕ) ⊆ Finset.range (L + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega), tent_eq t h0.le, tent_eq t h0.le, if_pos rfl, if_neg (by omega), if_pos rfl]
    push_cast; ring
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [tent_eq t h0.le, if_neg hx.1, if_neg hx.2, mul_zero]

theorem mul_eq_mul_of_pow_eq_pow {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {P x : Γ₀} (hP0 : P ≠ 0) (hP1 : P < 1)
    {a b c d : ℕ} (h1 : x ^ a = P ^ b) (h2 : x ^ c = P ^ d) : b * c = d * a := by
  have h3 : P ^ (b * c) = P ^ (d * a) := by
    calc P ^ (b * c) = (P ^ b) ^ c := pow_mul _ _ _
      _ = (x ^ a) ^ c := by rw [h1]
      _ = x ^ (a * c) := (pow_mul _ _ _).symm
      _ = x ^ (c * a) := by rw [mul_comm]
      _ = (x ^ c) ^ a := pow_mul _ _ _
      _ = (P ^ d) ^ a := by rw [h2]
      _ = P ^ (d * a) := (pow_mul _ _ _).symm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h3 (ne_of_gt (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hP0) hP1 hlt))
  · exact absurd h3 (ne_of_lt (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hP0) hP1 hlt))

end SndTT

namespace TwistH

theorem sum_laplace_Ico (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Ico 1 n, (f (d - 1) - 2 * f d + f (d + 1)) = f 0 - f 1 - f (n - 1) + f n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), ih hm]
      obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

theorem tent_sum (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) = 1 := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hlt : δ < ⌊δ⌋₊ + 1 := Nat.lt_floor_add_one δ
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)

  have hterm : ∀ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then 1 - (δ - ⌊δ⌋₊) else 0) + (if d = ⌊δ⌋₊ + 1 then δ - ⌊δ⌋₊ else 0) := by
    intro d _
    by_cases h1 : d = ⌊δ⌋₊
    · subst h1
      have h2 : ¬ (⌊δ⌋₊ = ⌊δ⌋₊ + 1) := by omega
      rw [if_pos rfl, if_neg h2, add_zero, abs_of_nonneg (by linarith)]
      exact max_eq_right (by linarith)
    · rw [if_neg h1, zero_add]
      by_cases h2 : d = ⌊δ⌋₊ + 1
      · subst h2
        rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith)]
        push_cast
        rw [max_eq_right (by linarith)]
        ring
      · rw [if_neg h2]
        apply max_eq_left

        rcases Nat.lt_or_gt_of_ne h1 with h | h
        ·
          have : (d : ℚ) + 1 ≤ ⌊δ⌋₊ := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]
          linarith
        ·
          have : (⌊δ⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast (show ⌊δ⌋₊ + 2 ≤ d by omega)
          rw [abs_of_nonpos (by linarith)]
          linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' , Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]

    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h4]; simp

theorem tent_one (d : ℕ) : max 0 (1 - |(1 : ℚ) - (d : ℚ)|) = if d = 1 then 1 else 0 := by
  by_cases h : d = 1
  · subst h; simp
  · rw [if_neg h]
    apply max_eq_left
    rcases Nat.lt_or_gt_of_ne h with h0 | h2
    · have : d = 0 := by omega
      subst this; simp
    · have : (2 : ℚ) ≤ d := by exact_mod_cast h2
      rw [abs_of_nonpos (by linarith)]; linarith

section Degree

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_support (h1 : ∀ V : Place K F, V.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ V ∈ D.support, D V := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Divisor.degree_single, h1]
  simp

theorem degree_filter (h1 : ∀ V : Place K F, V.deg = 1) (D : Divisor K F) (q : Place K F → Prop) [DecidablePred q] :
    Divisor.degree (D.filter q) = ∑ V ∈ D.support with q V, D V := by
  classical
  rw [degree_eq_sum_support h1, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finsupp.filter_apply_pos]
  exact (Finset.mem_filter.mp hV).2

end Degree

section JH

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
variable (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))

theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)}
    (h1 : Psp.IsStrictFst α β hα hβ δ V) : ¬ Psp.IsStrictSnd α β hα hβ δ V := fun h2 =>
  h1.2 (show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
      (Psp.reduceFst α hα V))) = Psp.reduceFst α hα V by rw [h1.1, ← h2.1])

open Classical in

theorem degree_decomp₀ (h1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Divisor.degree D = Divisor.degree (Psp.fstDiv α β hα hβ δ D) + Divisor.degree (Psp.sndDiv α β hα hβ δ D) +
      ∑ V ∈ D.support with (¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V), D V := by
  have hF : Divisor.degree (Psp.fstDiv α β hα hβ δ D) = ∑ V ∈ D.support with Psp.IsStrictFst α β hα hβ δ V, D V := by
    unfold JHPlaceSpecialization.fstDiv; convert degree_filter h1 D (Psp.IsStrictFst α β hα hβ δ)
  have hS : Divisor.degree (Psp.sndDiv α β hα hβ δ D) = ∑ V ∈ D.support with Psp.IsStrictSnd α β hα hβ δ V, D V := by
    unfold JHPlaceSpecialization.sndDiv; convert degree_filter h1 D (Psp.IsStrictSnd α β hα hβ δ)
  rw [hF, hS, degree_eq_sum_support h1]
  have step1 := (Finset.sum_filter_add_sum_filter_not D.support (Psp.IsStrictFst α β hα hβ δ) (fun V => D V)).symm
  have step2 := (Finset.sum_filter_add_sum_filter_not (D.support.filter fun V => ¬ Psp.IsStrictFst α β hα hβ δ V)
    (Psp.IsStrictSnd α β hα hβ δ) (fun V => D V)).symm
  rw [step1, step2, Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  refine Finset.sum_congr (Finset.filter_congr fun V _ => ?_) fun _ _ => rfl
  exact ⟨fun h => h.2, fun h => ⟨fun h' => not_isStrictSnd_of_isStrictFst Psp α β hα hβ δ h' h, h⟩⟩

open Classical in

theorem degree_decomp (h1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom →
      ¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V)
    (hdisj : ∀ (s s' : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom → V ∈ (An s').dom → s = s')
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hgood : ∀ V ∈ D.support, Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom) :
    Divisor.degree D = Divisor.degree (Psp.fstDiv α β hα hβ δ D) + Divisor.degree (Psp.sndDiv α β hα hβ δ D) +
      ∑ s : ↥SS, ∑ V ∈ D.support with V ∈ (An s).dom, D V := by
  rw [degree_decomp₀ Psp α β hα hβ δ h1 D]
  congr 1
  have key : ∀ V ∈ D.support,
      (if (¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V) then D V else 0)
        = ∑ s : ↥SS, if V ∈ (An s).dom then D V else 0 := by
    intro V hV
    by_cases h : ∃ s : ↥SS, V ∈ (An s).dom
    · obtain ⟨s₀, hs₀⟩ := h
      rw [if_pos (hAn s₀ V hs₀), Finset.sum_eq_single s₀ (fun s _ hne => if_neg (fun hs => hne (hdisj s s₀ V hs hs₀)))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hs₀]
    · have hstrict : ¬ (¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V) := by
        intro hn
        apply h
        rcases hgood V hV with h' | h' | h'
        · exact absurd h' hn.1
        · exact absurd h' hn.2
        · exact h'
      rw [if_neg hstrict]
      symm
      exact Finset.sum_eq_zero fun s _ => if_neg (fun hs => h ⟨s, hs⟩)
  rw [Finset.sum_filter, Finset.sum_congr rfl key, Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => (Finset.sum_filter _ _).symm

variable (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)

open Classical in

noncomputable def tentFn (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : ℚ :=
  if V ∈ (An s).dom then max 0 (1 - |pos s V - d|) else 0

noncomputable def circleHom (s : ↥SS) (d : ℕ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →+ ℚ :=
  Finsupp.liftAddHom fun V => (AddMonoidHom.mulRight (tentFn SS An pos s d V)).comp (Int.castAddHom ℚ)

open Classical in
theorem circleDeg_eq_circleHom (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) (d : ℕ) :
    JHPlaceSpecialization.twistCircleDeg SS An pos D s d = circleHom SS An pos s d D := by
  unfold JHPlaceSpecialization.twistCircleDeg circleHom
  rw [Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  unfold tentFn
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mulRight, Function.comp_apply, Int.coe_castAddHom]
  split_ifs <;> simp

theorem circleHom_single (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (n : ℤ) :
    circleHom SS An pos s d (Finsupp.single V n) = n * tentFn SS An pos s d V := by
  unfold circleHom
  rw [Finsupp.liftAddHom_apply_single]
  simp

open Classical in
theorem tentFn_of_not_mem (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (h : V ∉ (An s).dom) :
    tentFn SS An pos s d V = 0 := by
  unfold tentFn
  rw [if_neg h]

open Classical in

theorem tentFn_of_strict (s : ↥SS) (d : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hAn : V ∈ (An s).dom → ¬ Psp.IsStrictFst α β hα hβ δ V ∧ ¬ Psp.IsStrictSnd α β hα hβ δ V)
    (h : Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V) :
    tentFn SS An pos s d V = 0 := by
  apply tentFn_of_not_mem
  intro hmem
  rcases h with h | h
  · exact (hAn hmem).1 h
  · exact (hAn hmem).2 h

end JH

end TwistH

set_option maxHeartbeats 3200000 in
open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hFixRegFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hFixRegSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))

    (e' : ℕ) (he' : 0 < e')
    (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ)
    (hdepth : ∀ (s : ↥SS), ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, V ∈ (An s).dom →
      A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * ((An s).param)⁻¹)) ^ e' =
        A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ depth V)

    (hread : ∀ s₀ : ↥SS,
      componentGroupProj (fun s : ↥SS => e' * e s)
          (Psp.depthDual α hα SS depth (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) +
            Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) •
              (((e' * e s₀ : ℕ) : ℤ) • crossingCoord s₀)) = 0) :
    Psp.IsTwistType α (θ.toAlgHom.comp α) hα hβ δ SS e An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
  classical
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  have hdeg1all : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1 := fun V =>
    ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
      (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl V
  have hint : ∀ (w : ↥SS) (d : ℕ), (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d).den = 1 :=
    ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn An hAn pos hpos hposσ X hXst

  have hdomns : ∀ (w : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An w).dom → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V :=
    fun w V hV => ⟨((hAn w).1 V |>.mp hV).2.1, ((hAn w).1 V |>.mp hV).2.2⟩
  have hdomr : ∀ (w : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An w).dom → Psp.reduceFst α hα V = w.1.1 := fun w V hV => ((hAn w).1 V |>.mp hV).1
  have hX1 : ∀ s ∈ SS, ∀ s' ∈ SS, s.1 = s'.1 → s = s' := by
    intro s hs s' hs' h
    have h2 := (mem_ssNodePairsQExp_iff _).mp ((hSS s).mp hs)
    have h2' := (mem_ssNodePairsQExp_iff _).mp ((hSS s').mp hs')
    have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1
    exact Prod.ext h (hinj (h2.2.symm.trans (h.trans h2'.2)))
  have hdisj : ∀ (s s' : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom → V ∈ (An s').dom → s = s' := fun s s' V h h' =>
    Subtype.ext (hX1 s.1 s.2 s'.1 s'.2 ((hdomr s V h).symm.trans (hdomr s' V h')))
  have hX2 : ∀ s ∈ SS, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = s.1 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V := by
    intro s hs V hV
    have h2 := (mem_ssNodePairsQExp_iff _).mp ((hSS s).mp hs)
    have hfix2 := hFix s.2 h2.1
    have hFixed1 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ s.1 := by
      rw [h2.2]; exact hfix2.2
    have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1
    refine ⟨fun hst => hst.2 (hV ▸ hFixed1), fun hst => hst.2 ?_⟩
    have h3 : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.2 := hst.1.symm.trans (hV.trans h2.2)
    rw [hinj h3]
    exact hfix2.1

  have hgood_of : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom := by
    intro V h
    rcases h with h | h | ⟨s, hs, hV⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨⟨s, hs⟩, ((hAn ⟨s, hs⟩).1 V).mpr ⟨hV, hX2 s hs V hV⟩⟩)
  have hXgood : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s : ↥SS, V ∈ (An s).dom := fun V hV => hgood_of V (hXsupp V hV)

  have hposb : ∀ (w : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An w).dom → 0 < pos w V ∧ pos w V < e w := fun w V hV => ⟨(hpos w V hV).1, (hpos w V hV).2.1⟩
  have hw1 : ∀ w : ↥SS, 1 ≤ e w := fun w => he w

  have hintM : ∀ w : ↥SS, (JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w).den = 1 :=
    ModularCurve.JHPlaceSpecialization.den_twistPosMoment_eq_one_of_inertiaStable_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn An hAn pos hpos hposσ X hXst

  obtain ⟨m, hm⟩ : ∃ m : ↥SS → ℕ → ℤ, m = fun w d => (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d).num := ⟨_, rfl⟩
  obtain ⟨Mm, hM⟩ : ∃ Mm : ↥SS → ℤ, Mm = fun w => (JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w).num := ⟨_, rfl⟩
  obtain ⟨annDeg, hann⟩ : ∃ annDeg : ↥SS → ℤ, annDeg = fun w => ∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An w).dom, (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V := ⟨_, rfl⟩
  have hm_cast : ∀ (w : ↥SS) (d : ℕ), (m w d : ℚ) = JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w d := fun w d => by
    rw [hm]; exact Rat.coe_int_num_of_den_eq_one (hint w d)
  have hM_cast : ∀ w : ↥SS, (Mm w : ℚ) = JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w := fun w => by
    rw [hM]; exact Rat.coe_int_num_of_den_eq_one (hintM w)

  have S1 : ∀ w : ↥SS, ∑ d ∈ Finset.range (e w + 1), m w d = annDeg w := by
    intro w
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Finset.sum_congr rfl fun d _ => hm_cast w d, hann]
    unfold JHPlaceSpecialization.twistCircleDeg
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [← Finset.mul_sum]
    have ht := hposb w V (Finset.mem_filter.mp hV).2
    have := SndTT.tent_sum_eq_one (L := e w) ht.1 ht.2
    unfold SndTT.tent at this
    rw [this, mul_one]
  have S2 : ∀ w : ↥SS, ∑ d ∈ Finset.range (e w + 1), (d : ℤ) * m w d = Mm w := by
    intro w
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Finset.sum_congr rfl fun d _ => by rw [hm_cast w d], hM_cast w]
    unfold JHPlaceSpecialization.twistCircleDeg JHPlaceSpecialization.twistPosMoment
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun V hV => ?_
    have ht := hposb w V (Finset.mem_filter.mp hV).2
    have := SndTT.tent_sum_mul_eq (L := e w) ht.1 ht.2
    unfold SndTT.tent at this
    calc ∑ d ∈ Finset.range (e w + 1), (d : ℚ) * (((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * max 0 (1 - |pos w V - d|))
        = ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * ∑ d ∈ Finset.range (e w + 1), (d : ℚ) * max 0 (1 - |pos w V - d|) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * pos w V := by rw [this]

  have hvp1 : A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) < 1 := by
    have hle : A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff]; exact A.nonunits_le hA
    refine lt_of_le_of_ne hle fun h1 => ?_
    have hmem : (((p : ℕ) : AlgebraicClosure ℚ)) ∈ A := (A.valuation_le_one_iff _).mp hle
    have hu : IsUnit (⟨_, hmem⟩ : ↥A) := (A.valuation_eq_one_iff ⟨_, hmem⟩).mpr h1
    exact (A.mem_nonunits_iff_exists_mem_maximalIdeal.mp hA).elim fun h hh => (IsLocalRing.mem_maximalIdeal _ |>.mp hh) hu
  have hvp0 : A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hposdepth : ∀ (w : ↥SS), ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, V ∈ (An w).dom → (e' : ℚ) * pos w V = depth V := by
    intro w V hV hVw
    have h1 := (hpos w V hVw).2.2
    have h2 := hdepth w V hV hVw

    have hq := hposb w V hVw
    have hinj : (pos w V).num.toNat * e' = depth V * (pos w V).den := SndTT.mul_eq_mul_of_pow_eq_pow hvp0 hvp1 h1 h2
    have hnum : ((pos w V).num.toNat : ℤ) = (pos w V).num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq.1.le)
    have hden : ((pos w V).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos w V).den_nz
    have hq' : pos w V = (pos w V).num / (pos w V).den := (Rat.num_div_den _).symm
    have hinjQ : ((pos w V).num : ℚ) * e' = depth V * (pos w V).den := by
      have := congrArg (fun n : ℕ => (n : ℚ)) hinj
      push_cast at this
      rw [← hnum]; push_cast; exact this
    rw [hq']
    field_simp
    linarith [hinjQ]

  have hT : ∀ w : ↥SS, (Psp.depthDiv α hα depth (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 = (e' : ℤ) * Mm w := by
    intro w
    have e1 : (Psp.depthDiv α hα depth (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 =
        ∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with Psp.reduceFst α hα V = (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1, (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V * (depth V : ℤ) := by
      unfold JHPlaceSpecialization.depthDiv
      rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun V _ => by rw [Finsupp.single_apply]
    have e2 : ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support.filter fun V => Psp.reduceFst α hα V = (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1) = (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support.filter fun V => V ∈ (An w).dom := by
      ext V
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hV, hVw⟩
        exact ⟨hV, ((hAn w).1 V).mpr ⟨hVw, hX2 w.1 w.2 V hVw⟩⟩
      · rintro ⟨hV, hVw⟩; exact ⟨hV, hdomr w V hVw⟩
    rw [e1, e2]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hM_cast w]
    unfold JHPlaceSpecialization.twistPosMoment
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun V hV => ?_
    obtain ⟨hVs, hVw⟩ := Finset.mem_filter.mp hV
    rw [← hposdepth w V hVs hVw]
    ring

  obtain ⟨w₀⟩ : Nonempty ↥SS := by
    have hpN : ¬ p ∣ M / p := by
      intro h; apply hpM2; obtain ⟨k, hk⟩ := h
      exact ⟨k, by rw [pow_two, mul_assoc, ← hk, mul_comm, Nat.div_mul_cancel hpM]⟩
    obtain ⟨y, hy⟩ := ModularCurve.nonempty_ssPlacesQExp (M / p) (JHNeronObjectAtP.ΓN p M H hpM)
      (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)) (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)) p hpN (ResidueField ↥A)
    refine ⟨⟨(qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y, y), (hSS _).mpr ?_⟩⟩
    exact (mem_ssNodePairsQExp_iff _).mpr ⟨hy, rfl⟩
  have hunpack : ∃ (γ : ↥SS → ℤ) (κ' : ℤ), (∑ w, γ w = 0) ∧
      ∀ w : ↥SS, Mm w + (if w = w₀ then Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) * (e w₀ : ℤ) else 0) = (e w : ℤ) * γ w + κ' := by
    obtain ⟨α', hα'⟩ : ∃ α' : ↥SS → ℤ, α' = fun (s : ↥SS) => (Psp.depthDiv α hα depth (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 +
        (if s = w₀ then Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) * ((e' * e w₀ : ℕ) : ℤ) else 0) := ⟨_, rfl⟩
    have hfun : (∑ s, α' s • crossingCoord s : Module.Dual ℤ (characterLattice ↥SS))
        = Psp.depthDual α hα SS depth (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) • (((e' * e w₀ : ℕ) : ℤ) • crossingCoord w₀) := by
      unfold JHPlaceSpecialization.depthDual
      rw [hα']
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
    have hmem : (∑ s, α' s • crossingCoord s : Module.Dual ℤ (characterLattice ↥SS)) ∈ LinearMap.range (gramMap fun s : ↥SS => e' * e s) := by
      rw [hfun]
      exact (Submodule.Quotient.mk_eq_zero _).mp (hread w₀)
    obtain ⟨γ, κ, hγ0, hγ⟩ := SndTT.exists_coeff_of_mem_range_gramMap (fun s : ↥SS => e' * e s) α' hmem
    have hcoef : ∀ w : ↥SS, (e' : ℤ) * Mm w + (if w = w₀ then Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) * ((e' * e w₀ : ℕ) : ℤ) else 0)
        = ((e' * e w : ℕ) : ℤ) * γ w + κ := by
      intro w
      have h1 := hγ w
      rw [hα'] at h1
      simp only [] at h1
      rw [hT w] at h1
      exact h1
    have hdvd : (e' : ℤ) ∣ κ := by
      have h1 := hcoef w₀
      rw [if_pos rfl] at h1
      have : κ = (e' : ℤ) * Mm w₀ + Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) * ((e' * e w₀ : ℕ) : ℤ) - ((e' * e w₀ : ℕ) : ℤ) * γ w₀ := by
        linarith
      rw [this]
      push_cast
      exact Dvd.intro (Mm w₀ + Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) * (e w₀ : ℤ) - (e w₀ : ℤ) * γ w₀) (by ring)
    obtain ⟨κ', hκ'⟩ := hdvd
    refine ⟨γ, κ', hγ0, fun w => ?_⟩
    have h1 := hcoef w
    rw [hκ'] at h1
    have he0 : (e' : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr he'.ne'
    apply mul_left_cancel₀ he0
    by_cases hw0 : w = w₀
    · subst hw0
      rw [if_pos rfl] at h1 ⊢
      push_cast at h1 ⊢
      linarith
    · rw [if_neg hw0] at h1 ⊢
      push_cast at h1 ⊢
      linarith
  obtain ⟨γ, κ', hγ0, hγ⟩ := hunpack

  obtain ⟨sw, hs⟩ : ∃ sw : ↥SS → ℤ,
      sw = fun w => annDeg w - m w 0 - γ w + (if w = w₀ then Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) else 0) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ↥SS → ℕ → ℤ,
      v = fun w (d : ℕ) => (d : ℤ) * sw w - ∑ j ∈ Finset.range d, ((d : ℤ) - j) * m w j + (d : ℤ) * m w 0 := ⟨_, rfl⟩
  have hv0 : ∀ w, v w 0 = 0 := fun w => by rw [hv]; simp
  have hv1 : ∀ w, v w 1 = sw w := fun w => by rw [hv]; simp
  have hstep : ∀ w (d : ℕ), v w (d + 1) - v w d = sw w - ∑ j ∈ Finset.range (d + 1), m w j + m w 0 := by
    intro w d
    rw [hv]
    simp only
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : ∑ j ∈ Finset.range d, (((d + 1 : ℕ) : ℤ) - j) * m w j
        = ∑ j ∈ Finset.range d, ((d : ℤ) - j) * m w j + ∑ j ∈ Finset.range d, m w j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e1]
    push_cast
    ring
  have hsecond : ∀ w (d : ℕ), 1 ≤ d → v w (d - 1) - 2 * v w d + v w (d + 1) = -m w d := by
    intro w d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have h1 := hstep w (d' + 1)
    have h2 := hstep w d'
    rw [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ] at h1
    linarith

  have hvL : ∀ w : ↥SS, v w (e w) = κ' := by
    intro w
    have hS1 := S1 w
    have hS2 := S2 w
    have hγw := hγ w
    rw [Finset.sum_range_succ] at hS1 hS2
    rw [hv]
    simp only
    have e1 : ∑ j ∈ Finset.range (e w), ((e w : ℤ) - j) * m w j
        = (e w : ℤ) * ∑ j ∈ Finset.range (e w), m w j - ∑ j ∈ Finset.range (e w), (j : ℤ) * m w j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, hs]
    simp only
    by_cases hw0 : w = w₀
    · subst hw0
      simp only [if_true] at hγw ⊢
      nlinarith [hS1, hS2, hγw]
    · simp only [if_neg hw0] at hγw ⊢
      nlinarith [hS1, hS2, hγw]

  have hchain : ∀ (w : ↥SS) (d : ℕ), d ≤ e w →
      JHPlaceSpecialization.twistChainVal SS e (⟨0, κ', v⟩ : JHPlaceSpecialization.TwistVec ↥SS) w d = v w d := by
    intro w d hd
    unfold JHPlaceSpecialization.twistChainVal
    by_cases hd0 : d = 0
    · subst hd0; simp [hv0]
    · rw [if_neg hd0]
      by_cases hLd : e w ≤ d
      · rw [if_pos hLd]
        have : d = e w := le_antisymm hd hLd
        rw [this, hvL w]
      · rw [if_neg hLd]
  refine ⟨⟨0, κ', v⟩, ?_, ?_, ?_⟩
  ·
    have hend : ∀ w : ↥SS, JHPlaceSpecialization.twistEndOrderFst SS e An pos ⟨0, κ', v⟩ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w = annDeg w - γ w + (if w = w₀ then Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) else 0) := by
      intro w
      unfold JHPlaceSpecialization.twistEndOrderFst JHPlaceSpecialization.twistEndShareFst
      rw [hchain w 1 (hw1 w), hchain w 0 (Nat.zero_le _), hv1, hv0, if_pos (hint w 0)]
      rw [hs, hm]
      simp only
      ring
    rw [Finset.sum_congr rfl fun w _ => hend w, Finset.sum_add_distrib, Finset.sum_sub_distrib, hγ0, Finset.sum_ite_eq' Finset.univ w₀, if_pos (Finset.mem_univ _)]
    have hpart := TwistH.degree_decomp Psp α (θ.toAlgHom.comp α) hα hβ δ hdeg1all SS An (fun s V hV => hdomns s V hV) hdisj (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) hXgood
    rw [Divisor.mem_degZero.mp X.2] at hpart
    have hann' : ∑ w : ↥SS, annDeg w = ∑ s : ↥SS, ∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V := by rw [hann]
    linarith
  ·
    have hend : ∀ w : ↥SS, JHPlaceSpecialization.twistEndOrderSnd SS e An pos ⟨0, κ', v⟩ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w = γ w - (if w = w₀ then Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) else 0) := by
      intro w
      unfold JHPlaceSpecialization.twistEndOrderSnd JHPlaceSpecialization.twistEndShareSnd
      have hLw := hw1 w
      rw [hchain w (e w - 1) (by omega), hchain w (e w) le_rfl, if_pos (hint w _)]
      have hst := hstep w (e w - 1)
      have hsub : e w - 1 + 1 = e w := by omega
      rw [hsub] at hst
      have hS1 := S1 w
      rw [← hsub, Finset.sum_range_succ, hsub] at hS1
      rw [show (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) w (e w)).num = m w (e w) by rw [hm]]
      have : v w (e w - 1) - v w (e w) = -(sw w - ∑ j ∈ Finset.range (e w), m w j + m w 0) := by linarith
      rw [this, hs]
      simp only
      linarith
    rw [Finset.sum_congr rfl fun w _ => hend w, Finset.sum_sub_distrib, hγ0, Finset.sum_ite_eq' Finset.univ w₀, if_pos (Finset.mem_univ _)]
    ring
  ·
    intro w d hd1 hdL
    rw [hchain w (d - 1) (by omega), hchain w d (by omega), hchain w (d + 1) (by omega), hsecond w d hd1, ← hm_cast w d]
    push_cast
    ring

end

end S_ModularCurve_JHPlaceSpecialization_isTwistType_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isTwistType_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_annulus (solution)
