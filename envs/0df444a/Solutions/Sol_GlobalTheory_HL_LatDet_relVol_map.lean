-- Prove2me | solution 1 for GlobalTheory.HL.LatDet.relVol_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:14.7618+00:00
-- url     : https://prove2.me/submissions/da6054c5-cb78-40c2-984b-611b75bb744b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Theorems.Thm_GlobalTheory_HL_LatDet_resQ_ne_zero
import Theorems.Thm_GlobalTheory_HL_LatDet_relIndex_map
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_UpperTheory_Reformulated_B_Yzb5_relIndex_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatDet
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.LatDet
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {W : Type} [AddCommGroup W] [Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (φ : W ≃ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ), LinearMap.det (φ : W →ₗ[F] W) = (ϖ : F) ^ a * ((u : 𝒪[F]) : F) → ∀ W0 : AddSubgroup W, (∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) → (W0.map φ.toAddEquiv.toAddMonoidHom).relIndex W0 ≠ 0 ∧ W0.relIndex (W0.map φ.toAddEquiv.toAddMonoidHom) ≠ 0 ∧ relVol W0 (W0.map φ.toAddEquiv.toAddMonoidHom) = (resQ ϖ : ℝ) ^ (-a) := by
  intro F _ _ _ _ ϖ hϖ W _ _ ι _ b φ a u hd W0 hW
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hq := resQ_ne_zero hϖ
  haveI := Module.Finite.of_basis b
  haveI := Module.Free.of_basis b
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[F])
    (fun ij : ι × ι => b.repr (φ (b ij.2)) ij.1)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero c.2) hϖ
  set d := Module.finrank F W
  set t : F := (ϖ : F) ^ n with ht
  have htO : t ∈ 𝒪[F] := pow_mem ϖ.2 n
  have h1 : ∀ i j, b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    obtain ⟨y, hy⟩ := hc (i, j)
    have e1 : t = ((v : 𝒪[F]) : F) * ((c : 𝒪[F]) : F) := by
      rw [ht, mul_comm]; exact_mod_cast congrArg (fun x : 𝒪[F] => (x : F)) hv.symm
    have e2 : b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i = ((v : 𝒪[F]) : F) * (y : F) := by
      have hy' : (y : F) = ((c : 𝒪[F]) : F) * b.repr (φ (b j)) i := hy
      rw [hy', ← mul_assoc, ← e1]
      simp
    rw [e2]
    exact mul_mem (v : 𝒪[F]).2 y.2
  have h2 : ∀ i j, b.repr ((t • (LinearMap.id : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs
    · simpa using htO
    · simp
  obtain ⟨m1, hm1, i1⟩ := relIndex_map hϖ b _ (n * d + a) u (by
    rw [LinearMap.det_smul, hd, zpow_add₀ h0, ht, ← pow_mul, ← zpow_natCast, mul_assoc]
    push_cast; rfl) W0 hW h1
  obtain ⟨m2, hm2, i2⟩ := relIndex_map hϖ b _ (n * d) 1 (by
    rw [LinearMap.det_smul, LinearMap.det_id, ht, ← pow_mul, ← zpow_natCast]
    push_cast; rfl) W0 hW h2
  set A := W0.map φ.toAddEquiv.toAddMonoidHom with hA
  set B := W0.map (t • (φ : W →ₗ[F] W)).toAddMonoidHom with hB
  have hBe : B = (W0.map (t • (LinearMap.id : W →ₗ[F] W)).toAddMonoidHom).map
      φ.toAddEquiv.toAddMonoidHom := by
    rw [hB, AddSubgroup.map_map]
    congr 1
    ext x
    simp
  have i3 : B.relIndex A = resQ ϖ ^ m2 := by
    rw [hBe, hA, AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective, i2]
  have hle : ∀ ψ : W →ₗ[F] W, (∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) →
      W0.map ψ.toAddMonoidHom ≤ W0 := by
    rintro ψ hψ _ ⟨x, hx, rfl⟩
    rw [hW]
    intro i
    have : b.repr (ψ.toAddMonoidHom x) i = ∑ j, b.repr x j * b.repr (ψ (b j)) i := by
      change b.repr (ψ x) i = _
      conv_lhs => rw [← b.sum_repr x, map_sum, map_sum, Finsupp.finset_sum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    exact sum_mem fun j _ => mul_mem ((hW x).1 hx j) (hψ i j)
  have hBW : B ≤ W0 := hle _ h1
  have hBA : B ≤ A := by
    rw [hBe, hA]; exact AddSubgroup.map_mono (hle _ h2)
  have t1 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) W0 (le_inf hBA hBW) inf_le_right
  have t2 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) A (le_inf hBA hBW) inf_le_left
  rw [AddSubgroup.inf_relIndex_right, i1] at t1
  rw [AddSubgroup.inf_relIndex_left, i3] at t2
  have n1 := mul_ne_zero_iff.1 (t1 ▸ pow_ne_zero m1 hq)
  have n2 := mul_ne_zero_iff.1 (t2 ▸ pow_ne_zero m2 hq)
  refine ⟨n1.2, n2.2, ?_⟩
  have hq' : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast hq
  have c0 : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast n1.1
  have t1' : (B.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = (resQ ϖ : ℝ) ^ m1 := by exact_mod_cast t1
  have t2' : (B.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = (resQ ϖ : ℝ) ^ m2 := by exact_mod_cast t2
  have ea : -a = (m2 : ℤ) - m1 := by omega
  unfold relVol
  rw [ea, zpow_sub₀ hq', zpow_natCast, zpow_natCast, ← t1', ← t2', mul_div_mul_left _ _ c0]
end GlobalTheory.HL.LatDet
