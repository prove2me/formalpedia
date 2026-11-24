-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Sphere.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:12.326926+00:00
-- url     : https://prove2.me/submissions/69069ac3-9c1b-4391-90c2-8681e07c2865

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCard
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HermSp_norm_perp
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HermSp_perpEquiv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Sphere
namespace GlobalTheory.CompanionTheory.UnrDens.Sphere
theorem _root_.solution {E : Type} [CommRing E] {τ : E →+* E} [Fintype E] {V : Type} [AddCommGroup V]
    [Module E V] [Finite V] (B : HermSp E τ V) {w : V} (hw : IsUnit (B.h w w)) (c : E) :
    Nat.card {v : V // B.h v v = c} =
      ∑ a : E, Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} := by
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  have e1 : {x : E × B.perp w // (B.perpForm hw).h x.2 x.2 = c - x.1 * τ x.1 * B.h w w} ≃
      {v : V // B.h v v = c} :=
    Equiv.subtypeEquiv (B.perpEquiv hw) (by
      rintro ⟨a, v⟩
      have hv : B.h (v : V) w = 0 := v.2
      simp only [HermSp.perpEquiv_apply, HermSp.perpForm_h]
      rw [B.norm_perp hv a]
      constructor
      · intro h; rw [h]; ring
      · intro h; rw [← h]; ring)
  exact e1.symm.trans
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun s => ⟨(s.1, s.2.1), s.2.2⟩, fun _ => rfl, fun _ => rfl⟩
end GlobalTheory.CompanionTheory.UnrDens.Sphere
