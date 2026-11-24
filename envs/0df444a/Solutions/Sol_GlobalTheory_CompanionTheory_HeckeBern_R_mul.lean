-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.R_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:52.662915+00:00
-- url     : https://prove2.me/submissions/3edca93f-2fa9-4009-862a-cddf5becbbdb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_q_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_mul_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
variable (T : G → Hk K) (hp : IsHeckePair K)
variable (h1 : ∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) →
    (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) =
      ∑ y ∈ S, Finsupp.single y (1 : ℂ))
  (h3 : ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0)
include h1
include h3
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution {g h u : G} (H : ∀ k ∈ K, ∃ a ∈ K, ∃ b ∈ K, h * k * g = a * u * b) :
    R T hp g * R T hp h = R T hp u := by
  have hg := q_ne hp g
  have hh := q_ne hp h
  have hu := q_ne hp u
  rw [R, R, R, smul_mul_smul_comm, mul_of T hp h1 h3 H, smul_smul]
  congr 1
  field_simp
end GlobalTheory.CompanionTheory.HeckeBern
