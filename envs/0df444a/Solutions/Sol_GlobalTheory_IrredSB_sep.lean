-- Prove2me | solution 1 for GlobalTheory.IrredSB.sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:37.867974+00:00
-- url     : https://prove2.me/submissions/86dce1a1-8a3a-414f-a9c3-a19e82aad56a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_IrredSB_exists_sep
import Theorems.Thm_GlobalTheory_IrredSB_pair_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [Fintype Y']
namespace GlobalTheory.IrredSB
theorem _root_.solution [CharZero k] (ψk : AddChar k Circle) (hψ : Continuous ψk) (h1 : ψk ≠ 1) {n : ℕ} (hn : 0 < n)
    (p : Matrix Y Y' k) (hp : p ∉ lat k Y Y' n) :
    ∃ b, (∀ u ∈ lat k Y Y' n, (ψk (pair b u) : ℂ) = 1) ∧ (ψk (pair b p) : ℂ) ≠ 1 := by
  classical
  have hn' : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  have : ¬ ∀ r q, (n : k)⁻¹ * p r q ∈ 𝒪[k] := fun h => hp ⟨(n : k)⁻¹ • p, h, by
    show n • (n : k)⁻¹ • p = p
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  push Not at this
  obtain ⟨r, q, hrq⟩ := this
  obtain ⟨b, hb, hb'⟩ := exists_sep ψk hψ h1 hrq
  refine ⟨Matrix.single r q (b * (n : k)⁻¹), ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [pair_single]
    have : b * (n : k)⁻¹ * (nsmulAddMonoidHom n u : Matrix Y Y' k) r q = b * u r q := by
      show b * (n : k)⁻¹ * (n • u r q) = b * u r q
      rw [nsmul_eq_mul]
      field_simp
    rw [this, hb _ (hu r q)]
    rfl
  · rw [pair_single, mul_assoc]
    exact fun h => hb' (Circle.ext h)
end GlobalTheory.IrredSB
