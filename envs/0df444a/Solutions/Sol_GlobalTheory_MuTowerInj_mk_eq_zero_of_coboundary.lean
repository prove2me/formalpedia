-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:02.83743+00:00
-- url     : https://prove2.me/submissions/c276d2f3-1c63-4f07-a495-d959d82a037d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
import Theorems.Thm_GlobalTheory_MuTowerInj_mapH2Add_mk
import Theorems.Thm_GlobalTheory_MuTowerInj_ker_le_range
import Theorems.Thm_GlobalTheory_MuTowerInj_injective_of_card
import Theorems.Thm_GlobalTheory_MuTowerInj_iota_apply
import Theorems.Thm_GlobalTheory_MuTowerInj_iota_injective
import Theorems.Thm_GlobalTheory_MuTowerInj_iota_mul
import Theorems.Thm_GlobalTheory_MuTowerInj_red_toZModPow
import Theorems.Thm_GlobalTheory_MuTowerInj_red_surjective
import Theorems.Thm_GlobalTheory_MuTowerInj_exists_iota_of_red
import Theorems.Thm_GlobalTheory_MuTowerInj_card_H2_muLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
namespace GlobalTheory.MuTowerInj
theorem _root_.solution : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  intro hD F Ω _ _ _ _ _ l _ A v hA n w a ha hrel

  have hu : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ 1)),
      iota l n (muLoc F l 1 A g m) = muLoc F l (n + 1) A g (iota l n m) := fun g m =>
    iota_mul l n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) m
  have hp : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ (n + 1))),
      (red l n).toAddMonoidHom (muLoc F l (n + 1) A g m) =
        muLoc F l n A g ((red l n).toAddMonoidHom m) := by
    intro g m
    show red l n (PadicInt.toZModPow (n + 1) ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * m) =
      PadicInt.toZModPow n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * red l n m
    rw [map_mul, red_toZModPow]
  have hcard : ∀ r, Nat.card (H2 (muLoc F l r A)) = l ^ r := card_H2_muLoc hD F Ω l A v hA
  have : ∀ r, Finite (H2 (muLoc F l r A)) := fun r =>
    Nat.finite_of_card_ne_zero (by rw [hcard r]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

  have hinj := injective_of_card
    (secondCohomologyMapOfEquivariantAdd (muLoc F l 1 A) (muLoc F l (n + 1) A) (iota l n) hu)
    (secondCohomologyMapOfEquivariantAdd (muLoc F l (n + 1) A) (muLoc F l n A) (red l n).toAddMonoidHom hp)
    (ker_le_range _ _ _ (GlobalTheory.TameQuot.contAction_muDec A l (n + 1)) _ hu _ hp
      (iota_injective l n) (red_surjective l n) (exists_iota_of_red l n))
    (by rw [hcard, hcard, hcard]; ring)
  apply hinj
  rw [map_zero, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨a, ha, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply]
  exact (hrel g h).trans (iota_apply l n _).symm
end GlobalTheory.MuTowerInj
