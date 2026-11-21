-- Prove2me | solution 2 for MasulloGRH.bounded_lifting_strict_nuclear_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:49:14.561267+00:00
-- url     : https://prove2.me/submissions/80a76d6e-53ef-4993-b3cc-098fd6afd836

import Theorems.Thm_MasulloGRH_bounded_lifting_of_stage_factorizations
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded
import Theorems.Thm_MasulloGRH_strictLF_quotient_stage_factorization

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsStrictLFOfNuclearFrechet E) (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hQ : IsStrictLFOfNuclearFrechet (E ⧸ V)) : LiftsBoundedSets (V.mkQ : E → E ⧸ V) := by
  obtain ⟨X, hXm, hXe, hX, hXt⟩ := hE
  obtain ⟨Y, hYm, hYe, hY, hYt⟩ := hQ
  have hA := strictLF_hlcs_and_closed_steps (E ⧸ V) Y hYm hYe (fun n => (hY n).1) hYt
  have hfac := fun n =>
    strictLF_quotient_stage_factorization E X hXm hXe hX hXt V hV Y hYm hYe hY hYt n
  choose k v hv using hfac
  exact bounded_lifting_of_stage_factorizations E (E ⧸ V) hA.1 Y hYm hYe hA.2 hYt
    (fun n => X (k n)) (fun n => X (k n) ⧸ V.comap (X (k n)).subtype)
    V.mkQ (fun n => (X (k n)).subtypeL) (fun n => (V.comap (X (k n)).subtype).mkQ)
    (fun n => Submodule.mapQ (V.comap (X (k n)).subtype) V (X (k n)).subtype le_rfl) v
    (fun n => nuclear_frechet_quotient_lifts_bounded _ (hX (k n)).1 (hX (k n)).2 _
       (hV.preimage continuous_subtype_val))
    (fun n x => rfl) hv
