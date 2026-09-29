-- Prove2me | solution 1 for ModularCurve.heckePic0BarTranspose_fricke_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e0c0b447-f03a-59d3-bd08-5970bf9c08eb

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckePic0BarTranspose_fricke_smul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_qExpand"
open scoped Pointwise

namespace W7ATransposeFricke

section CrossTransport

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable {g : SemilinearAut K F} {g' : SemilinearAut K F'}
variable {φ ψ : F →ₐ[K] F'}

def CrossIntertwines (φ ψ : F →ₐ[K] F') (g : SemilinearAut K F) (g' : SemilinearAut K F') :
    Prop :=
  ∀ x : F, g' • (φ x) = ψ (g • x)

theorem CrossIntertwines.inv (h : CrossIntertwines φ ψ g g') :
    CrossIntertwines ψ φ g⁻¹ g'⁻¹ := by
  intro x
  have hx := h (g⁻¹ • x)
  rw [smul_inv_smul] at hx
  rw [← hx, inv_smul_smul]

theorem restrictAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).restrictAlong ψ hψ = g • w.restrictAlong φ hφ := by
  apply Place.toValuationSubring_injective
  ext x
  change ψ x ∈ (g' • w).toValuationSubring ↔
    x ∈ (g • w.restrictAlong φ hφ).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, h.inv x]
  rfl

private theorem _root_.W7ATransposeFricke.ord_smul (h : CrossIntertwines φ ψ g g') (w : Place K F') (f : F) :
    (g' • w).ord (ψ f) = w.ord (φ (g⁻¹ • f)) := by
  have : ψ f = g' • φ (g⁻¹ • f) := by rw [h, smul_inv_smul]
  rw [this, SemilinearAut.ord_smul]

p2m_export "W7ATransposeFricke" "ord_smul"

theorem ramificationIndexAlong_smul (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).ramificationIndexAlong ψ = w.ramificationIndexAlong φ := by
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  change sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (g' • w).ord (ψ f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (φ f) = n}
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    exact ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], by rw [← ord_smul h, hford]⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    rw [ord_smul h, inv_smul_smul, hford]

def restrictEquiv (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring ≃+*
      ((g' • w).restrictAlong ψ hψ).toValuationSubring where
  toFun x := ⟨g • (x : F), by
    have hx : φ (x : F) ∈ w.toValuationSubring := x.2
    show ψ (g • (x : F)) ∈ (g' • w).toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring, ← h (x : F)]
    exact ValuationSubring.smul_mem_pointwise_smul g' _ _ hx⟩
  invFun y := ⟨g⁻¹ • (y : F), by
    have hy : ψ (y : F) ∈ (g' • w).toValuationSubring := y.2
    show φ (g⁻¹ • (y : F)) ∈ w.toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
    rw [← h.inv (y : F)]
    exact hy⟩
  left_inv x := by ext; exact inv_smul_smul g (x : F)
  right_inv y := by ext; exact smul_inv_smul g (y : F)
  map_mul' x y := by ext; exact smul_mul' g (x : F) (y : F)
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)

theorem inertiaDegAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).inertiaDegAlong ψ hψ = w.inertiaDegAlong φ hφ := by
  letI iφ : Algebra (w.restrictAlong φ hφ).ResidueField w.ResidueField :=
    (letI := algebraAlong φ; haveI := isScalarTower_along φ; haveI := isIntegral_along φ hφ
     (Place.restrictResidueMap F w).toAlgebra)
  letI iψ : Algebra ((g' • w).restrictAlong ψ hψ).ResidueField (g' • w).ResidueField :=
    (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; haveI := isIntegral_along ψ hψ
     (Place.restrictResidueMap F (g' • w)).toAlgebra)
  change Module.finrank ((g' • w).restrictAlong ψ hψ).ResidueField (g' • w).ResidueField
    = Module.finrank (w.restrictAlong φ hφ).ResidueField w.ResidueField
  refine (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (restrictEquiv hφ hψ h w))
    (SemilinearAut.smulResidueRingEquiv g' w) ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.residue (g' • w).toValuationSubring
      (⟨ψ (g • (a : F)), _⟩ : (g' • w).toValuationSubring)
    = IsLocalRing.residue (g' • w).toValuationSubring
      (⟨g' • φ (a : F), _⟩ : (g' • w).toValuationSubring)
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (h (a : F)).symm)

theorem pullbackAlong_smul [HasPrincipalDivisors K F'] (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (h : CrossIntertwines φ ψ g g') (D : Divisor K F) :
    Divisor.pullbackAlong ψ hψ (g • D) = g' • Divisor.pullbackAlong φ hφ D := by
  ext w
  rw [Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    SemilinearAut.divisor_smul_apply, Divisor.pullbackAlong_apply,
    restrictAlong_smul hψ hφ h.inv w, ramificationIndexAlong_smul h.inv w]

theorem pushforwardAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (E : Divisor K F') :
    Divisor.pushforwardAlong ψ hψ (g' • E) = g • Divisor.pushforwardAlong φ hφ E := by
  induction E using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [SemilinearAut.smul_single, Divisor.pushforwardAlong_single,
      Divisor.pushforwardAlong_single, SemilinearAut.smul_single,
      restrictAlong_smul hφ hψ h w, inertiaDegAlong_smul hφ hψ h w]

theorem correspondence_smul_exchange [HasPrincipalDivisors K F']
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h₁ : CrossIntertwines φ ψ g g') (h₂ : CrossIntertwines ψ φ g g') (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence ψ φ hψ hφ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    pullbackAlong_smul hψ hφ h₂ D, pushforwardAlong_smul hφ hψ h₁]

theorem pic0_correspondence_smul_exchange [HasPrincipalDivisors K F']
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    (h₁ : CrossIntertwines φ ψ g g') (h₂ : CrossIntertwines ψ φ g g') (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ (g • c)
      = g • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [SemilinearAut.pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk,
    SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_degZeroCorrespondence, SemilinearAut.coe_degZeroSMulHom,
    SemilinearAut.coe_degZeroSMulHom, Pic0.coe_degZeroCorrespondence]
  exact correspondence_smul_exchange hφ hψ h₁ h₂ (D : Divisor K F)

end CrossTransport

section Modular

local notation "Qb" => AlgebraicClosure ℚ

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
      = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]

theorem modularFunctionFieldBar_eq_adjoin (M : ℕ) :
    modularFunctionFieldBar M
      = IntermediateField.adjoin Qb (coeffEmb Qb '' divisorExpansions M) := by
  apply le_antisymm
  · change laurentBaseChange Qb (modularFunctionFieldFull M) ≤ _
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ _) at hy
    have hy' : coeffEmb Qb y ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M)).map (coeffEmb Qb) :=
      ⟨y, hy, rfl⟩
    rw [RingHom.map_field_closure] at hy'
    refine (Subfield.closure_le (t := (IntermediateField.adjoin Qb
      (coeffEmb Qb '' divisorExpansions M)).toSubfield)).mpr ?_ hy'
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨c, rfl⟩ | hx
    · rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange Qb (IntermediateField.subset_adjoin ℚ _ hx)

theorem algHom_ext_bar (M : ℕ) {E : Type*} [Semiring E] [Algebra Qb E]
    {f g : modularFunctionFieldBar M →ₐ[Qb] E}
    (h : ∀ (d : ℕ) [NeZero d], d ∣ M → ∀ x : modularFunctionFieldBar M,
      (x : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ d jq) → f x = g x) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qb (modularFunctionFieldBar_eq_adjoin M) ?_
  rintro _ ⟨x, ⟨d, hne, hd, rfl⟩, rfl⟩
  exact h d hd _ rfl

variable {N ℓ : ℕ} [NeZero N] [NeZero ℓ]

def FrickeSpec (M : ℕ) (σ : modularFunctionFieldBar M ≃ₐ[Qb] modularFunctionFieldBar M) : Prop :=
  ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = M →
    ∀ x : modularFunctionFieldBar M,
      (x : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ a jq) →
        ((σ x : modularFunctionFieldBar M) : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ b jq)

variable {σ : modularFunctionFieldBar N ≃ₐ[Qb] modularFunctionFieldBar N}
variable {σ' : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}

theorem fricke_comp_alpha (hσ : FrickeSpec N σ) (hσ' : FrickeSpec (N * ℓ) σ') :
    σ'.toAlgHom.comp (heckeAlphaBar Qb N ℓ) = (heckeBetaBar Qb N ℓ).comp σ.toAlgHom := by
  refine algHom_ext_bar N fun d _ hd x hx => Subtype.ext ?_
  obtain ⟨e, rfl⟩ := hd
  haveI : NeZero e := ⟨fun h => NeZero.ne (d * e) (by rw [h, mul_zero])⟩
  haveI : NeZero (ℓ * e) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne e)⟩
  have h1 : ((σ' (heckeAlphaBar Qb (d * e) ℓ x) : modularFunctionFieldBar (d * e * ℓ)) :
      LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ (ℓ * e) jq) :=
    hσ' d (ℓ * e) (by ring) _ (by rw [coe_heckeAlphaBar, hx])
  have h2 : ((σ x : modularFunctionFieldBar (d * e)) : LaurentSeries Qb)
      = coeffEmb Qb (qExpand ℚ e jq) := hσ d e rfl x hx
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, coe_heckeBetaBar]
  rw [h1, h2, ← coeffEmb_qExpand, qExpand_qExpand]

theorem fricke_comp_beta (hσ : FrickeSpec N σ) (hσ' : FrickeSpec (N * ℓ) σ') :
    σ'.toAlgHom.comp (heckeBetaBar Qb N ℓ) = (heckeAlphaBar Qb N ℓ).comp σ.toAlgHom := by
  refine algHom_ext_bar N fun d _ hd x hx => Subtype.ext ?_
  obtain ⟨e, rfl⟩ := hd
  haveI : NeZero e := ⟨fun h => NeZero.ne (d * e) (by rw [h, mul_zero])⟩
  haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
  have h1 : ((σ' (heckeBetaBar Qb (d * e) ℓ x) : modularFunctionFieldBar (d * e * ℓ)) :
      LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ e jq) :=
    hσ' (ℓ * d) e (by ring) _ (by rw [coe_heckeBetaBar, hx, ← coeffEmb_qExpand, qExpand_qExpand])
  have h2 : ((σ x : modularFunctionFieldBar (d * e)) : LaurentSeries Qb)
      = coeffEmb Qb (qExpand ℚ e jq) := hσ d e rfl x hx
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, coe_heckeAlphaBar]
  rw [h1, h2]

theorem crossIntertwines_alpha_beta (hσ : FrickeSpec N σ) (hσ' : FrickeSpec (N * ℓ) σ') :
    CrossIntertwines (heckeAlphaBar Qb N ℓ) (heckeBetaBar Qb N ℓ)
      (SemilinearAut.ofAlgAut σ) (SemilinearAut.ofAlgAut σ') := fun x => by
  rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
  exact AlgHom.congr_fun (fricke_comp_alpha hσ hσ') x

theorem crossIntertwines_beta_alpha (hσ : FrickeSpec N σ) (hσ' : FrickeSpec (N * ℓ) σ') :
    CrossIntertwines (heckeBetaBar Qb N ℓ) (heckeAlphaBar Qb N ℓ)
      (SemilinearAut.ofAlgAut σ) (SemilinearAut.ofAlgAut σ') := fun x => by
  rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
  exact AlgHom.congr_fun (fricke_comp_beta hσ hσ') x

end Modular

end W7ATransposeFricke

open W7ATransposeFricke in
theorem solution (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
          ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq))
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfinα)
    (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hfinβ)
    (x : JZero N) :
    heckePic0BarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut σ • x)
      = SemilinearAut.ofAlgAut σ • heckePic0Bar hα hβ hFIβ hfinα hNα x := by
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  obtain ⟨σ', hσ'⟩ := ModularCurve.exists_frickeAlgEquiv_modularFunctionFieldBar (N * ℓ)
  have hσ0 : FrickeSpec N σ := fun a b _ _ hab x hx => hσ a b hab x hx
  have hσ'0 : FrickeSpec (N * ℓ) σ' := fun a b _ _ hab x hx => hσ' a b hab x hx
  exact pic0_correspondence_smul_exchange hα hβ hFIα hfinβ hNβ hFIβ hfinα hNα
    (crossIntertwines_alpha_beta hσ0 hσ'0) (crossIntertwines_beta_alpha hσ0 hσ'0) x

end S_ModularCurve_heckePic0BarTranspose_fricke_smul
end P2MW
export P2MW.S_ModularCurve_heckePic0BarTranspose_fricke_smul (solution)
