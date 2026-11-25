-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.moves_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:34.249802+00:00
-- url     : https://prove2.me/submissions/15cf9954-7efa-4edc-94ba-b849214077f1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_grp_apply
import Theorems.Thm_GlobalTheory_HL_CoordDatum_set_iff
import Theorems.Thm_GlobalTheory_HL_CoordDatum_isUnitary_and_fixes_frames_of_mem_complementUnitary
import Theorems.Thm_GlobalTheory_HL_CoordDatum_perp_iff
import Theorems.Thm_GlobalTheory_HL_CoordDatum_smul_set_iff
import Theorems.Thm_GlobalTheory_HL_CoordDatum_inn_move
import Theorems.Thm_GlobalTheory_HL_CoordDatum_mem_gr
import Theorems.Thm_P2M_GlobalTheory_HL_CoordDatum_mem_gr__4f04eac64afc
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordDatum
theorem _root_.solution (g : V ≃ₗ[E] V) (hg : g ∈ P.UW0) (d d' : LocNG.Datum P) :
    LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d' := by
  obtain ⟨hu, hf⟩ := (set_iff c g).2 ((isUnitary_and_fixes_frames_of_mem_complementUnitary c g).1 hg)
  have hA := perp_iff P.A.f g hu fun b => (hf b).1
  have hB := perp_iff P.B.f g hu fun b => (hf b).2
  have hsplit : c.grp g • c.dat d = c.dat d' ↔
      c.grp g • c.inn P.A.f d.L = c.inn P.A.f d'.L ∧ c.grp g • c.inn P.B.f d.L' = c.inn P.B.f d'.L' ∧
        c.grp g • (c.dat d).2.2 = (c.dat d').2.2 := by
    rw [Prod.ext_iff, Prod.ext_iff]; rfl
  have h3 : c.grp g • (c.dat d).2.2 = (c.dat d').2.2 ↔
      ∀ (x' y' : ↥(H.perp (H.X P.B.f))) (x y : ↥(H.perp (H.X P.A.f))), (y' : V) = g x' → (y : V) = g x →
        (Q d x' x ↔ Q d' y' y) := by
    rw [smul_set_iff]
    constructor
    · intro h x' y' x y h1 h2
      rw [← mem_gr' c, ← mem_gr' c, h, grp_apply, grp_apply, h1, h2]
    · intro h v' v
      obtain ⟨v, rfl⟩ := c.e.surjective v
      obtain ⟨v', rfl⟩ := c.e.surjective v'
      rw [grp_apply, grp_apply, mem_gr, mem_gr]
      exact ⟨fun ⟨hv', hv, h1⟩ => ⟨(hB v').2 hv', (hA v).2 hv,
          (h ⟨v', hv'⟩ ⟨_, (hB v').2 hv'⟩ ⟨v, hv⟩ ⟨_, (hA v).2 hv⟩ rfl rfl).1 h1⟩,
        fun ⟨hv', hv, h1⟩ => ⟨(hB v').1 hv', (hA v).1 hv,
          (h ⟨v', (hB v').1 hv'⟩ ⟨_, hv'⟩ ⟨v, (hA v).1 hv⟩ ⟨_, hv⟩ rfl rfl).2 h1⟩⟩
  rw [hsplit, h3, ← inn_move c _ g hA, ← inn_move c _ g hB]
  unfold LocNG.Datum.Moves
  refine and_congr_right fun h1 => and_congr_right fun h2 => ?_
  refine forall₄_congr fun x' y' x y => forall₂_congr fun e1 e2 => ?_
  unfold Q
  by_cases hs : M.split = none
  · simp [d.io_L hs, d'.io_L hs, hs, h1 x y e2, h2 x' y' e1]
  · simp [hs]
end GlobalTheory.HL.CoordDatum
