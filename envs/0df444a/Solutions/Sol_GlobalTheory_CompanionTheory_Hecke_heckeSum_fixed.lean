-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:25.447143+00:00
-- url     : https://prove2.me/submissions/e2782aac-7cd3-4a98-bc47-0c0730eb5e55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeSumInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hecke
namespace GlobalTheory.CompanionTheory.Hecke
theorem _root_.solution :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite →
      (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) →
      ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  intro G V _ _ _ ρ K f hfin hbi v hv k hk
  have hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite := by
    refine hfin.subset ?_
    intro q hq h0
    apply hq
    have h0' : f q.out = 0 := h0
    simp [h0']
  have hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v)
      = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v := by
    intro q
    have hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K :=
      QuotientGroup.eq.mp hmk.symm
    obtain ⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ :=
      ⟨_, hκ, by group⟩
    rw [hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]
    simp [hv κ hκK]
  have h1 := (ρ k).toAddMonoidHom.map_finsum hsupp
  have h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v)
      = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v) := h1
  rw [h2, finsum_congr hstep]
  exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)
end GlobalTheory.CompanionTheory.Hecke
