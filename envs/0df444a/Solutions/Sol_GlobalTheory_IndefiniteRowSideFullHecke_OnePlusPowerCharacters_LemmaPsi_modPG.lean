-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi.modPG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:54.359382+00:00
-- url     : https://prove2.me/submissions/10f1269f-3b7a-4f9b-8b37-a1cefe847795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_OnePlusPowerAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam
namespace GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
namespace LemmaPsi
theorem _root_.solution (h : LemmaPsi) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (hl : 5 ≤ l)
    (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (hι : IsCyclotomic R ι) :
    ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, IsPsi l ι ψ ∧ PsiRing R ψ ∧
      ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
        [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
        [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V) (i : ZMod n),
        ∃ Ψ : V →ₗ[k] V, PsiMod l ψ (D.φ i) (D.γ (i - 1)) (D.γ i) Ψ := by
  obtain ⟨-, ψ, h1, h2, h3⟩ := h l k hl R ι hι
  refine ⟨ψ, h1, h2, fun n V _ _ _ _ _ _ _ _ D i => ?_⟩
  exact h3 V _ _ _ (D.φ_semi i) (D.etale i) (D.γ_semi _) (D.γ_semi _) (D.comm i)
end LemmaPsi
end GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
