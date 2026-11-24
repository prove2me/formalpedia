-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:09.472169+00:00
-- url     : https://prove2.me/submissions/a963b708-e603-4359-9ae3-5bfab0c1e9c6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_X
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_perp
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_N
import Theorems.Thm_GlobalTheory_HL_CoordUnip_theta_eq
import Theorems.Thm_GlobalTheory_HL_CoordUnip_psi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), LocNG.theta M = S.th ∧ (∀ g, g ∈ P.A.N ↔ c.grp g ∈ S.N) ∧ (∀ g, g ∈ P.B.N ↔ c.grp g ∈ S.N') ∧ (∀ g, g ∈ P.St ↔ c.grp g ∈ S.St) ∧ (∀ g, P.A.psiN (LocNG.theta M) g = S.psi (c.grp g) ∧ P.B.psiN (LocNG.theta M) g = S.psi' (c.grp g)) ∧ (∀ x, x ∈ H.X P.A.f ↔ c.e x ∈ S.X) ∧ (∀ x, x ∈ H.X P.B.f ↔ c.e x ∈ S.X') ∧ (∀ x, x ∈ H.perp (H.X P.A.f) ↔ c.e x ∈ perp M.L S.Hm S.X) ∧ ∀ x, x ∈ H.perp (H.X P.B.f) ↔ c.e x ∈ perp M.L S.Hm S.X' := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c
  refine ⟨theta_eq c, fun g => mem_N c P.A S.f c.f_eq g, fun g => mem_N c P.B S.f' c.f'_eq g, ?_,
    fun g => ⟨psi_eq c P.A S.f S.es c.f_eq c.es_eq g, psi_eq c P.B S.f' S.es' c.f'_eq c.es'_eq g⟩,
    fun x => mem_X S c.e P.A S.f c.f_eq x, fun x => mem_X S c.e P.B S.f' c.f'_eq x,
    fun x => mem_perp S c.e P.A S.f c.h_eq c.f_eq x, fun x => mem_perp S c.e P.B S.f' c.h_eq c.f'_eq x⟩
  intro g
  rw [LocNG.FPair.St, Frames.St, Subgroup.mem_inf, Subgroup.mem_inf, mem_N c P.A S.f c.f_eq,
    mem_N c P.B S.f' c.f'_eq]
  rfl
end GlobalTheory.HL.CoordUnip
