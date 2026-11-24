-- Prove2me | solution 1 for GlobalTheory.LevQuot.exists_liftAut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:28.641124+00:00
-- url     : https://prove2.me/submissions/cd40e78a-d0e2-45df-85dd-16a90d8f84c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
namespace GlobalTheory.LevQuot
theorem _root_.solution {P Q : Scheme.{0}} {φ : P ⟶ Q} {p : P ⟶ X} {q : Q ⟶ Y} {r : X ⟶ Y} (h : IsPullback φ p q r) :
    ∃ τ : autOver r →* Aut P, ∀ ω, (τ ω).hom ≫ φ = φ ∧ (τ ω).hom ≫ p = p ≫ ω.1.hom := by
  have hom_r : ∀ ω : autOver r, ω.1.hom ≫ r = r := fun ω => ω.2
  have inv_r : ∀ ω : autOver r, ω.1.inv ≫ r = r := fun ω => (Iso.inv_comp_eq ω.1).2 (hom_r ω).symm
  have sq : ∀ u : X ⟶ X, u ≫ r = r → φ ≫ q = (p ≫ u) ≫ r := fun u hu => by
    rw [Category.assoc, hu, h.w]
  have back : ∀ (u v : X ⟶ X) (hu : u ≫ r = r) (hv : v ≫ r = r), u ≫ v = 𝟙 X →
      h.lift φ (p ≫ u) (sq u hu) ≫ h.lift φ (p ≫ v) (sq v hv) = 𝟙 P := fun u v hu hv huv => by
    apply h.hom_ext
    · simp
    · simp only [Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc, huv, Category.comp_id,
        Category.id_comp]
  let lift1 : autOver r → Aut P := fun ω =>
    { hom := h.lift φ (p ≫ ω.1.hom) (sq _ (hom_r ω))
      inv := h.lift φ (p ≫ ω.1.inv) (sq _ (inv_r ω))
      hom_inv_id := back _ _ (hom_r ω) (inv_r ω) ω.1.hom_inv_id
      inv_hom_id := back _ _ (inv_r ω) (hom_r ω) ω.1.inv_hom_id }
  refine ⟨{ toFun := lift1, map_one' := ?_, map_mul' := ?_ }, fun ω => ⟨h.lift_fst _ _ _, h.lift_snd _ _ _⟩⟩
  · ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = 𝟙 P ≫ φ
      rw [IsPullback.lift_fst, Category.id_comp]
    · change h.lift _ _ _ ≫ p = 𝟙 P ≫ p
      rw [IsPullback.lift_snd, Category.id_comp]
      exact Category.comp_id p
  · intro a b
    ext1
    apply h.hom_ext
    · change h.lift _ _ _ ≫ φ = (h.lift φ (p ≫ b.1.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.hom) (sq _ (hom_r a))) ≫ φ
      simp only [IsPullback.lift_fst, Category.assoc]
    · change h.lift _ _ _ ≫ p = (h.lift φ (p ≫ b.1.hom) (sq _ (hom_r b)) ≫
        h.lift φ (p ≫ a.1.hom) (sq _ (hom_r a))) ≫ p
      simp only [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd_assoc]
      rfl
end GlobalTheory.LevQuot
