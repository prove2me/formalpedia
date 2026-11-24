-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:23.269034+00:00
-- url     : https://prove2.me/submissions/1cc2ea39-27f4-4708-a253-ecfe28f260c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_baer_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (h : Alt c) {L A : AddSubgroup W} (hLA : L ≤ A) (hL : ∀ x ∈ L, ∀ y ∈ L, c x y = 1) (hA : A ≤ h.perp A) :
    ∃ α : W → ℂ, Splits c A α ∧ ∀ x ∈ L, α x = 1 := by
  classical
  let b : A →+ A →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (Units.mk0 (c x y) (h.ne _ _)))
      fun y z => Additive.toMul.injective (Units.ext (by simp [h.right])))
    fun x y => by
      ext z
      simp [h.left]
  have hbv : ∀ x y, ((b x y).toMul : ℂ) = c x y := fun x y => rfl
  have hb : ∀ x y, b x y = b y x := fun x y => Additive.toMul.injective (Units.ext (by
    rw [hbv, hbv]
    exact mul_left_cancel₀ (h.ne x y) (by rw [h.anti, ← pow_two]; exact hA x.2 y y.2)))
  let f : L × Additive ℂˣ →+ Tw b hb := AddMonoidHom.mk' (fun p => ⟨⟨p.1, hLA p.1.2⟩, p.2⟩) fun p q => Tw.ext rfl (by
    show p.2 + q.2 = p.2 + q.2 + b _ _
    rw [left_eq_add]
    exact Additive.toMul.injective (Units.ext (hL _ p.1.2 _ q.1.2)))
  have hf : Function.Injective f := fun p q hpq =>
    Prod.ext (Subtype.ext (congrArg (fun g : Tw b hb => g.pt.1) hpq)) (congrArg Tw.sc hpq)
  obtain ⟨g, hg⟩ := baer_units.extension_property_addMonoidHom f hf (AddMonoidHom.snd _ _)
  have hg' : ∀ p, g (f p) = p.2 := fun p => DFunLike.congr_fun hg p
  refine ⟨fun x => if hx : x ∈ A then ((g ⟨⟨x, hx⟩, 0⟩).toMul : ℂ) else 1, ⟨fun a ha => ?_, fun a ha a' ha' => ?_⟩, fun x hx => ?_⟩
  · simp [ha]
  · rw [dif_pos ha, dif_pos ha', dif_pos (A.add_mem ha ha')]
    have h1 : (⟨⟨a, ha⟩, 0⟩ + ⟨⟨a', ha'⟩, 0⟩ : Tw b hb) = f (0, b ⟨a, ha⟩ ⟨a', ha'⟩) + ⟨⟨a + a', A.add_mem ha ha'⟩, 0⟩ :=
      Tw.ext (Subtype.ext (zero_add _).symm) (by
        show 0 + 0 + b ⟨a, ha⟩ ⟨a', ha'⟩ = b ⟨a, ha⟩ ⟨a', ha'⟩ + 0 + b 0 _
        simp)
    have h2 := congrArg (fun t => ((g t).toMul : ℂ)) h1
    simpa only [map_add, toMul_add, Units.val_mul, hg', hbv] using h2
  · beta_reduce
    rw [dif_pos (hLA hx)]
    exact congrArg (fun t : Additive ℂˣ => (t.toMul : ℂ)) (hg' (⟨x, hx⟩, 0))
end GlobalTheory.Published.SvN
