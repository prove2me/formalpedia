-- Prove2me | solution 1 for GlobalTheory.SBInduced.sb_induced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:46.795856+00:00
-- url     : https://prove2.me/submissions/cdf87024-bb84-4ba6-8484-428925818179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatEventuallyInvariantOfContinuousAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInduced
import Theorems.Thm_GlobalTheory_SBInduced_isClosedEmbedding_translate
import Theorems.Thm_GlobalTheory_SBInduced_descend
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_schwartzBruhat_eventually_invariant_of_continuous_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter
open GlobalTheory GlobalTheory.SBInduced
variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]
namespace GlobalTheory.SBInduced
theorem _root_.solution : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  intro G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev
  have hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1 := IsOpen.mem_nhds hχ (one_mem χ.ker)
  have hce := isClosedEmbedding_translate r h1 hm hc hj
  let A : SB X → G → SB Y := fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g),
    Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩
  have hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun _ _ _ => rfl
  have hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w' := fun w w' h =>
    ev.injective (Subtype.ext (funext h))
  let T : SB X →ₗ[ℂ] smoothPart (ind P σ) :=
    { toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by
          rw [hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul,
            mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'
          refine Subtype.ext (funext fun g => ?_)
          show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)
          congr 1
          refine Subtype.ext (funext fun y => ?_)
          rw [hA, hA, map_mul, hu, mul_one, hm, hu'])⟩
      map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)
        rw [← map_add]
        congr 1
        exact Subtype.ext (funext fun y => mul_add _ _ _)))
      map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)
        rw [← map_smul]
        congr 1
        exact Subtype.ext (funext fun y => mul_left_comm _ _ _))) }
  have hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun Φ g y => by
    show (ev (ev.symm (A Φ g))).1 y = _
    rw [ev.apply_symm_apply, hA]
  have hinj : Function.Injective T := fun Φ Ψ h => Subtype.ext (funext fun x => by
    obtain ⟨y, c, -, rfl⟩ := hs x
    have := hT Φ c y
    rw [h, hT] at this
    exact (mul_left_cancel₀ (χ c).ne_zero this).symm)
  have hsurj : Function.Surjective T := fun F => by
    have hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x =>
        congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x
    obtain ⟨Φ, hΦ⟩ := descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g))
      (by
        filter_upwards [hχ', hF] with u hu hu' g
        rw [hu', map_mul, hu, mul_one])
      (fun y g y' g' h => by
        have h2 : r (j y) (g * g'⁻¹) = j y' := by rw [hm, h, ← hm, mul_inv_cancel, h1]
        have hp := hP _ _ _ h2
        have h3 : s y ⟨_, hp⟩ = y' := hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)
        have h4 := F.1.2 ⟨_, hp⟩ g'
        rw [show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g'] at h4
        show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'
        rw [h4, hev, h3]
        simp [← mul_assoc])
    refine ⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩
    rw [hT, hΦ]
    exact mul_inv_cancel_left₀ (χ g).ne_zero _
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩
end GlobalTheory.SBInduced
