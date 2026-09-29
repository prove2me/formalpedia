-- Prove2me | solution 1 for ModularForm.exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f783d6d9-75e8-5c19-8a5c-fb3a38a31668

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_PowerSeries_exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq"
p2m_attr_erase "simp" "CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open UpperHalfPlane ModularFormClass ModularCurve CongruenceSubgroup IsLocalRing
open scoped MatrixGroups ModularForm

namespace RedSpan

theorem exists_solution_of_exists_solution_map {k K : Type*} [Field k] [CommRing K] (ι : k →+* K)
    (hι : Function.Injective ι) {α : Type*} : ∀ (r : ℕ) (P : Fin r → α → k) (m : α → k) (d : Fin r → K),
    (∀ n, ∑ i, d i * ι (P i n) = ι (m n)) → ∃ e : Fin r → k, ∀ n, ∑ i, e i * P i n = m n := by
  intro r
  induction r with
  | zero =>
    intro P m d h
    refine ⟨fun i => i.elim0, fun n => ?_⟩
    have := h n
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at this ⊢
    exact hι (by rw [map_zero]; exact this)
  | succ r ih =>
    intro P m d h
    by_cases hl : ∀ n, P (Fin.last r) n = 0
    ·
      obtain ⟨e', he'⟩ := ih (fun i => P (Fin.castSucc i)) m (fun i => d (Fin.castSucc i)) (fun n => by
        have := h n
        rw [Fin.sum_univ_castSucc, hl n, map_zero, mul_zero, add_zero] at this
        exact this)
      refine ⟨fun i => Fin.lastCases 0 e' i, fun n => ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, zero_mul, add_zero]
      exact he' n
    · push Not at hl
      obtain ⟨n₀, hn₀⟩ := hl
      set L := P (Fin.last r) with hL

      let P' : Fin r → α → k := fun i n => P (Fin.castSucc i) n - (P (Fin.castSucc i) n₀ / L n₀) * L n
      let m' : α → k := fun n => m n - (m n₀ / L n₀) * L n
      let q : Fin r → K := fun i => ι (P (Fin.castSucc i) n₀ / L n₀)
      let qm : K := ι (m n₀ / L n₀)
      have hq : ∀ i, q i * ι (L n₀) = ι (P (Fin.castSucc i) n₀) := fun i => by
        show ι _ * ι _ = _; rw [← map_mul, div_mul_cancel₀ _ hn₀]
      have hqm : qm * ι (L n₀) = ι (m n₀) := by
        show ι _ * ι _ = _; rw [← map_mul, div_mul_cancel₀ _ hn₀]
      have h0 := h n₀
      rw [Fin.sum_univ_castSucc] at h0
      have hu : IsUnit (ι (L n₀)) := (IsUnit.mk0 _ hn₀).map ι
      have key : d (Fin.last r) + ∑ i : Fin r, d (Fin.castSucc i) * q i = qm := by
        apply hu.mul_right_cancel
        rw [hqm, ← h0, add_mul, Finset.sum_mul, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hq i]
      have h' : ∀ n, ∑ i, d (Fin.castSucc i) * ι (P' i n) = ι (m' n) := by
        intro n
        have hn := h n
        rw [Fin.sum_univ_castSucc] at hn
        have e1 : ∑ i : Fin r, d (Fin.castSucc i) * ι (P (Fin.castSucc i) n) = ι (m n) - d (Fin.last r) * ι (L n) := by
          rw [← hn]; ring
        have e2 : ∑ i : Fin r, d (Fin.castSucc i) * ι (P' i n) =
            ∑ i : Fin r, d (Fin.castSucc i) * ι (P (Fin.castSucc i) n) - (∑ i : Fin r, d (Fin.castSucc i) * q i) * ι (L n) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [P', map_sub, map_mul]
          ring
        have e3 : ι (m' n) = ι (m n) - qm * ι (L n) := by simp only [m', qm, map_sub, map_mul]
        rw [e2, e3, e1]
        linear_combination (-(ι (L n))) * key
      obtain ⟨e', he'⟩ := ih P' m' (fun i => d (Fin.castSucc i)) h'

      refine ⟨fun i => Fin.lastCases ((m n₀ - ∑ j : Fin r, e' j * P (Fin.castSucc j) n₀) / L n₀) e' i, fun n => ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      have hen := he' n
      simp only [P', m', mul_sub, Finset.sum_sub_distrib] at hen
      have e4 : ∑ i : Fin r, e' i * (P (Fin.castSucc i) n₀ / L n₀ * L n) =
          (∑ i : Fin r, e' i * P (Fin.castSucc i) n₀) * (L n / L n₀) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e4] at hen
      rw [← hL]
      field_simp
      have hen' := hen
      field_simp at hen'
      linear_combination hen'

theorem intCast_mem_iff {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsPrime) {p : ℕ} (hp : p.Prime)
    (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪) (t : ℤ) : (t : integralClosure ℤ ℂ) ∈ 𝔪 ↔ (p : ℤ) ∣ t := by
  constructor
  · intro ht
    by_contra hnd
    have hnd' : ¬ p ∣ t.natAbs := fun h => hnd (Int.ofNat_dvd_left.mpr h)
    have hcop : IsCoprime (p : ℤ) (t.natAbs : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd')
    obtain ⟨u, v, huv⟩ := hcop
    have habs : ((t.natAbs : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪 := by
      rcases Int.natAbs_eq t with h | h
      · rw [← h]; exact ht
      · have : ((t.natAbs : ℤ) : integralClosure ℤ ℂ) = -(t : integralClosure ℤ ℂ) := by
          rw [eq_neg_iff_add_eq_zero, ← Int.cast_add, show (t.natAbs : ℤ) + t = 0 by omega, Int.cast_zero]
        rw [this]; exact 𝔪.neg_mem ht
    have h1 : (1 : integralClosure ℤ ℂ) = (u : integralClosure ℤ ℂ) * p + (v : integralClosure ℤ ℂ) * (t.natAbs : ℤ) := by
      have := congrArg (fun z : ℤ => (z : integralClosure ℤ ℂ)) huv
      push_cast at this ⊢
      exact this.symm
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr
      (h1 ▸ 𝔪.add_mem (𝔪.mul_mem_left _ hp𝔪) (𝔪.mul_mem_left _ habs)))
  · rintro ⟨s, rfl⟩
    push_cast
    exact 𝔪.mul_mem_right _ hp𝔪

theorem T_mem_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ModularForm Γ k) :
    (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, (⇑(f i) : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

theorem exists_valuationSubring_dominating {K : Type*} [Field K] (S : Subring K) (P : Ideal S) [P.IsPrime] :
    ∃ B : ValuationSubring K, (∀ z : S, (z : K) ∈ B) ∧ (∀ y : S, y ∉ P → ((y : K))⁻¹ ∈ B) ∧
      (∀ (x : S), x ∈ P → ∀ hx : (x : K) ∈ B, (⟨(x : K), hx⟩ : B) ∈ IsLocalRing.maximalIdeal B) := by
  let A₀ : LocalSubring K := LocalSubring.ofPrime S P
  obtain ⟨B, hB⟩ := A₀.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hB
  have memB : ∀ z : S, (z : K) ∈ B := fun z => hle (LocalSubring.le_ofPrime S P z.2)
  refine ⟨B, memB, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ P.primeCompl := hy
    have hu : IsUnit (algebraMap S A₀.toSubring y) := IsLocalization.map_units A₀.toSubring (⟨y, hy'⟩ : P.primeCompl)
    obtain ⟨w, hw⟩ := hu
    have hwv : ((w : A₀.toSubring) : K) = (y : K) := by rw [hw]; rfl
    have hprod : ((w : A₀.toSubring) : K) * (((w⁻¹ : (A₀.toSubring)ˣ) : A₀.toSubring) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hyinv : (y : K)⁻¹ = (((w⁻¹ : (A₀.toSubring)ˣ) : A₀.toSubring) : K) := by
      rw [← hwv]; exact (eq_inv_of_mul_eq_one_right hprod).symm
    rw [hyinv]
    exact hle ((w⁻¹ : (A₀.toSubring)ˣ) : A₀.toSubring).2
  · intro x hx hxB
    have hxA : (algebraMap S A₀.toSubring x) ∈ IsLocalRing.maximalIdeal A₀.toSubring :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff A₀.toSubring P x).mpr hx
    rw [IsLocalRing.mem_maximalIdeal] at hxA ⊢
    intro hunit
    apply hxA
    have : Subring.inclusion hle (algebraMap S A₀.toSubring x) = (⟨(x : K), hxB⟩ : B) := rfl
    exact (isUnit_map_iff (Subring.inclusion hle) _).mp (this ▸ hunit)

end RedSpan

open RedSpan in
theorem solution
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (k : ℤ)
    (p : ℕ) [Fact p.Prime] (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (Y : ModularForm (CohCarrier.GammaH N H') k)
    (hYint : ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff Y n)
    (hYred : ∀ n : ℕ, ∃ m : ℤ, ∀ x y : integralClosure ℤ ℂ, y ∉ 𝔪 → (x : ℂ) = y * qCoeff Y n →
      x - (m : integralClosure ℤ ℂ) * y ∈ 𝔪) :
    ∃ (Y' : ModularForm (CohCarrier.GammaH N H') k) (P : PowerSeries ℤ), ModularCurve.IsIntegralQExp Y' P ∧
      ∀ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪 → (x : ℂ) = y * qCoeff Y n →
        x - ((PowerSeries.coeff n P : ℤ) : integralClosure ℤ ℂ) * y ∈ 𝔪 := by
  classical
  have hp : p.Prime := Fact.out
  haveI := h𝔪
  have h1 := one_mem_strictPeriods_GammaH N H'
  set V : PowerSeries ℂ := qExpansion 1 ⇑Y with hVdef
  have hVn : ∀ n, PowerSeries.coeff n V = qCoeff (⇑Y) n := fun n => rfl
  choose mY hmY using hYred

  have hy0 : ∀ y : integralClosure ℤ ℂ, y ∉ 𝔪 → (y : ℂ) ≠ 0 := by
    intro y hy h
    apply hy
    have : y = 0 := Subtype.ext h
    rw [this]; exact 𝔪.zero_mem
  by_cases hV0 : V = 0
  ·
    refine ⟨0, 0, ?_, ?_⟩
    · show (0 : PowerSeries ℤ).map (Int.castRingHom ℂ) = qExpansion 1 ⇑(0 : ModularForm (CohCarrier.GammaH N H') k)
      rw [map_zero, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero]
    · intro n x y hy hx
      have : qCoeff (⇑Y) n = 0 := by rw [← hVn, hV0, map_zero]
      rw [this, mul_zero] at hx
      have hx0 : x = 0 := Subtype.ext hx
      simp [hx0]

  obtain ⟨Λ, hΛmem⟩ : ∃ Λ : AddSubgroup (PowerSeries ℤ),
      ∀ P, P ∈ Λ ↔ ∃ Z : ModularForm (CohCarrier.GammaH N H') k, IsIntegralQExp Z P := ⟨
    { carrier := {P | ∃ Z : ModularForm (CohCarrier.GammaH N H') k, IsIntegralQExp Z P}
      zero_mem' := ⟨0, by
        show (0 : PowerSeries ℤ).map (Int.castRingHom ℂ) = qExpansion 1 ⇑(0 : ModularForm (CohCarrier.GammaH N H') k)
        rw [map_zero, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero]⟩
      add_mem' := by
        rintro P P' ⟨Z, hZ⟩ ⟨Z', hZ'⟩
        refine ⟨Z + Z', ?_⟩
        show (P + P').map (Int.castRingHom ℂ) = qExpansion 1 ⇑(Z + Z')
        have : qExpansion 1 ⇑(Z + Z') = ModularForm.qExpansionAddHom one_pos h1 k (Z + Z') := rfl
        rw [this, map_add, map_add]
        exact congrArg₂ (· + ·) hZ hZ'
      neg_mem' := by
        rintro P ⟨Z, hZ⟩
        refine ⟨-Z, ?_⟩
        show (-P).map (Int.castRingHom ℂ) = qExpansion 1 ⇑(-Z)
        have : qExpansion 1 ⇑(-Z) = ModularForm.qExpansionAddHom one_pos h1 k (-Z) := rfl
        rw [this, map_neg, map_neg]
        exact congrArg (- ·) hZ }, fun P => Iff.rfl⟩
  have hΛsat : ∀ (n : ℤ) (P : PowerSeries ℤ), n ≠ 0 → n • P ∈ Λ → P ∈ Λ := by
    intro n P hn hnP
    obtain ⟨Z, hZ⟩ := (hΛmem _).mp hnP
    refine (hΛmem _).mpr ⟨((n : ℂ)⁻¹) • Z, ?_⟩
    show P.map (Int.castRingHom ℂ) = qExpansion 1 ⇑(((n : ℂ)⁻¹) • Z)
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1, ← hZ]
    rw [zsmul_eq_mul, map_mul, PowerSeries.smul_eq_C_mul, ← mul_assoc, map_intCast,
      show PowerSeries.C ((n : ℂ)⁻¹) * (n : PowerSeries ℂ) = 1 by
        rw [← map_intCast (PowerSeries.C (R := ℂ)) n, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hn), map_one],
      one_mul]

  have hVspan : V ∈ Submodule.span ℂ ((fun P : PowerSeries ℤ => P.map (Int.castRingHom ℂ)) '' (Λ : Set (PowerSeries ℤ))) := by
    obtain ⟨n, c, G, r, hG, hF⟩ := ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH N H' Y
    have hV' : V = ∑ i, c i • (r i).map (Int.castRingHom ℂ) := by
      have hcoe : (⇑Y : UpperHalfPlane → ℂ) = ⇑(∑ i, c i • G i) := by
        rw [hF, coe_finset_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ModularForm.IsGLPos.coe_smul]
      rw [hVdef, hcoe]
      have : qExpansion 1 ⇑(∑ i, c i • G i) = ModularForm.qExpansionAddHom one_pos h1 k (∑ i, c i • G i) := rfl
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show qExpansion 1 ⇑(c i • G i) = _
      rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1, (hG i)]
    rw [hV']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r i, (hΛmem _).mpr ⟨G i, hG i⟩, rfl⟩)

  obtain ⟨B, memB', inv_memB', mem_maxB'⟩ :=
    exists_valuationSubring_dominating (K := ℂ) (integralClosure ℤ ℂ).toSubring (𝔪 : Ideal ((integralClosure ℤ ℂ).toSubring))
  have memB : ∀ z : integralClosure ℤ ℂ, (z : ℂ) ∈ B := fun z => memB' ⟨(z : ℂ), z.2⟩
  have inv_memB : ∀ y : integralClosure ℤ ℂ, y ∉ 𝔪 → (y : ℂ)⁻¹ ∈ B := fun y hy => inv_memB' ⟨(y : ℂ), y.2⟩ hy
  have mem_maxB : ∀ x : integralClosure ℤ ℂ, x ∈ 𝔪 → (⟨(x : ℂ), memB x⟩ : B) ∈ IsLocalRing.maximalIdeal B :=
    fun x hx => mem_maxB' ⟨(x : ℂ), x.2⟩ hx (memB x)

  have hcoefB : ∀ n, PowerSeries.coeff n V ∈ B := by
    intro n
    obtain ⟨x, y, hy, hx⟩ := hYint n
    have : PowerSeries.coeff n V = (x : ℂ) * (y : ℂ)⁻¹ := by
      rw [hVn, hx]; field_simp [hy0 y hy]
    rw [this]
    exact B.mul_mem _ _ (memB x) (inv_memB y hy)

  have hcong : ∀ n, (⟨PowerSeries.coeff n V, hcoefB n⟩ : B) - ((mY n : ℤ) : B) ∈ IsLocalRing.maximalIdeal B := by
    intro n
    obtain ⟨x, y, hy, hx⟩ := hYint n
    have hm := hmY n x y hy hx

    have key : (⟨PowerSeries.coeff n V, hcoefB n⟩ : B) - ((mY n : ℤ) : B) =
        (⟨((x - (mY n : ℤ) * y : integralClosure ℤ ℂ) : ℂ), memB _⟩ : B) * ⟨(y : ℂ)⁻¹, inv_memB y hy⟩ := by
      apply Subtype.ext
      show PowerSeries.coeff n V - ((mY n : ℤ) : ℂ) = ((x - (mY n : ℤ) * y : integralClosure ℤ ℂ) : ℂ) * (y : ℂ)⁻¹
      rw [hVn]
      push_cast
      rw [hx]
      field_simp [hy0 y hy]
    rw [key]
    exact Ideal.mul_mem_right _ _ (mem_maxB _ hm)

  obtain ⟨c, u, hc0, hVcu, hu0, huspan⟩ :=
    PowerSeries.exists_eq_C_mul_map_and_mem_span_of_mem_span_of_saturated B Λ hΛsat hVspan hV0

  have hVu : ∀ n, PowerSeries.coeff n V = c * ((PowerSeries.coeff n u : B) : ℂ) := by
    intro n
    rw [hVcu, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
    rfl

  have hcB : c ∈ B := by
    have : ∃ n, PowerSeries.coeff n u ∉ IsLocalRing.maximalIdeal B := by
      by_contra hall
      push Not at hall
      apply hu0
      ext n
      rw [PowerSeries.coeff_map, map_zero]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr (hall n)
    obtain ⟨n₁, hn₁⟩ := this
    have hunit : IsUnit (PowerSeries.coeff n₁ u) := by
      by_contra h; exact hn₁ ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨w, hw⟩ := hunit
    have hw0 : ((PowerSeries.coeff n₁ u : B) : ℂ) ≠ 0 := by
      rw [← hw]; exact fun h => w.ne_zero (Subtype.ext h)
    have : c = PowerSeries.coeff n₁ V * (((w⁻¹ : Bˣ) : B) : ℂ) := by
      rw [hVu n₁, ← hw, mul_assoc, ← Subring.coe_mul B.toSubring, Units.mul_inv]
      simp
    rw [this]
    exact B.mul_mem _ _ (hcoefB n₁) ((w⁻¹ : Bˣ) : B).2

  obtain ⟨r, b, g, hbg⟩ := Submodule.mem_span_set'.mp huspan
  have hg : ∀ i, ∃ P : PowerSeries ℤ, P ∈ Λ ∧ P.map (Int.castRingHom B) = (g i : PowerSeries B) := by
    intro i
    obtain ⟨P, hP, hPeq⟩ := (g i).2
    exact ⟨P, hP, hPeq⟩
  choose Pi hPiΛ hPieq using hg
  have hZi : ∀ i, ∃ Z : ModularForm (CohCarrier.GammaH N H') k, IsIntegralQExp Z (Pi i) := fun i => (hΛmem _).mp (hPiΛ i)
  choose Zi hZi' using hZi

  have huB : ∀ n, PowerSeries.coeff n u = ∑ i, b i * ((PowerSeries.coeff n (Pi i) : ℤ) : B) := by
    intro n
    rw [← hbg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_smul, ← hPieq i, PowerSeries.coeff_map, smul_eq_mul]
    rfl
  have hcoefId : ∀ n, (⟨PowerSeries.coeff n V, hcoefB n⟩ : B) =
      ∑ i, (⟨c, hcB⟩ * b i) * ((PowerSeries.coeff n (Pi i) : ℤ) : B) := by
    intro n
    have : (⟨PowerSeries.coeff n V, hcoefB n⟩ : B) = ⟨c, hcB⟩ * PowerSeries.coeff n u := Subtype.ext (hVu n)
    rw [this, huB n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

  let κ := IsLocalRing.ResidueField B
  let red : B →+* κ := IsLocalRing.residue B
  have hpB : (⟨((p : integralClosure ℤ ℂ) : ℂ), memB _⟩ : B) ∈ IsLocalRing.maximalIdeal B := mem_maxB _ hp𝔪
  have hpκ : (p : κ) = 0 := by
    have : red (⟨((p : integralClosure ℤ ℂ) : ℂ), memB _⟩ : B) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hpB
    rw [← this, ← map_natCast red p]
    congr 1
  haveI : CharP κ p := (CharP.charP_iff_prime_eq_zero hp).mpr hpκ
  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hιint : ∀ t : ℤ, ι (t : ZMod p) = red (t : B) := by
    intro t; rw [map_intCast, map_intCast]

  have hrel : ∀ n, ∑ i, red (⟨c, hcB⟩ * b i) * ι ((PowerSeries.coeff n (Pi i) : ℤ) : ZMod p) = ι ((mY n : ℤ) : ZMod p) := by
    intro n
    have h := congrArg red (hcoefId n)
    rw [map_sum] at h
    have h2 : red (⟨PowerSeries.coeff n V, hcoefB n⟩ : B) = red ((mY n : ℤ) : B) := by
      rw [← sub_eq_zero, ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr (hcong n)
    rw [hιint, ← h2, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hιint, ← map_mul]
  have hex : ∃ e : Fin r → ZMod p, ∀ n : ℕ,
      ∑ i, e i * (((PowerSeries.coeff n (Pi i) : ℤ)) : ZMod p) = ((mY n : ℤ) : ZMod p) := by
    refine exists_solution_of_exists_solution_map (α := ℕ) ι (RingHom.injective ι) r _ _
      (fun i => red (⟨c, hcB⟩ * b i)) ?_
    exact hrel
  obtain ⟨e, he⟩ := hex

  let c' : Fin r → ℤ := fun i => ((e i).val : ℤ)
  have hc' : ∀ i, ((c' i : ℤ) : ZMod p) = e i := fun i => by simp [c']
  have hdvd : ∀ n, (p : ℤ) ∣ (∑ i, c' i * PowerSeries.coeff n (Pi i)) - mY n := by
    intro n
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [hc']
    rw [he n, sub_self]
  let P : PowerSeries ℤ := ∑ i, PowerSeries.C (c' i) * Pi i
  have hPn : ∀ n, PowerSeries.coeff n P = ∑ i, c' i * PowerSeries.coeff n (Pi i) := by
    intro n
    simp only [P, map_sum, PowerSeries.coeff_C_mul]
  let Y' : ModularForm (CohCarrier.GammaH N H') k := ∑ i, ((c' i : ℤ) : ℂ) • Zi i
  have hY'int : IsIntegralQExp Y' P := by
    show P.map (Int.castRingHom ℂ) = qExpansion 1 ⇑Y'
    have : qExpansion 1 ⇑Y' = ModularForm.qExpansionAddHom one_pos h1 k Y' := rfl
    rw [this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (PowerSeries.map (Int.castRingHom ℂ)) (PowerSeries.C (c' i) * Pi i) = qExpansion 1 ⇑(((c' i : ℤ) : ℂ) • Zi i)
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1, ← hZi' i, map_mul, PowerSeries.map_C,
      PowerSeries.smul_eq_C_mul]
    rfl
  refine ⟨Y', P, hY'int, fun n x y hy hx => ?_⟩

  have hsplit : x - ((PowerSeries.coeff n P : ℤ) : integralClosure ℤ ℂ) * y =
      (x - ((mY n : ℤ) : integralClosure ℤ ℂ) * y) - (((PowerSeries.coeff n P - mY n : ℤ) : integralClosure ℤ ℂ)) * y := by
    push_cast; ring
  rw [hsplit]
  refine 𝔪.sub_mem (hmY n x y hy hx) (𝔪.mul_mem_right _ ?_)
  rw [intCast_mem_iff h𝔪 hp hp𝔪, hPn]
  exact hdvd n

end S_ModularForm_exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH
end P2MW
export P2MW.S_ModularForm_exists_isIntegralQExp_qCoeff_congr_of_qCoeff_congr_intCast_gammaH (solution)
