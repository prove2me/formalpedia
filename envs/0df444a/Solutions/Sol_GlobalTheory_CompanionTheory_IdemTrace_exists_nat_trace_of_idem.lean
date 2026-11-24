-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IdemTrace.exists_nat_trace_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:18.356429+00:00
-- url     : https://prove2.me/submissions/6078c20c-e9da-47bd-b55f-829321c9e86f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IdemTrace
namespace GlobalTheory.CompanionTheory.IdemTrace
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ}
    (P : Matrix (Fin g) (Fin g) O) (h : P * P = P) :
    ∃ r : ℕ, r ≤ g ∧ Matrix.trace P = (r : O) ∧ (r = 0 → P = 0) := by
  classical
  set f : (Fin g → O) →ₗ[O] (Fin g → O) := Matrix.toLin' P with hf
  have hidem : IsIdempotentElem f := by
    unfold IsIdempotentElem
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have hff : ∀ z, f (f z) = f z := fun z => by
    rw [← Module.End.mul_apply, hidem.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem f).mpr hidem
  have hPr : Module.Projective O (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict
      (LinearMap.ext fun y => Subtype.ext (by
        obtain ⟨z, hz⟩ := y.2
        simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.id_apply]
        rw [← hz]
        exact hff z))
  let sK : (Fin g → O) →ₗ[O] LinearMap.ker f :=
    (LinearMap.id - f).codRestrict (LinearMap.ker f) (fun y => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hff, sub_self])
  have hsK : sK.comp (LinearMap.ker f).subtype = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by
      have hy : f y = 0 := y.2
      simp [sK, hy])
  have hPk : Module.Projective O (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype sK hsK
  have hFk : Module.Finite O (LinearMap.ker f) :=
    Module.Finite.of_surjective sK (fun y => ⟨y, by
      exact LinearMap.congr_fun hsK y⟩)
  have : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  have : Module.Free O (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  have htr := hproj.trace
  refine ⟨Module.finrank O (LinearMap.range f), ?_, ?_, ?_⟩
  · calc Module.finrank O (LinearMap.range f) ≤ Module.finrank O (Fin g → O) :=
          Submodule.finrank_le _
      _ = g := Module.finrank_fin_fun O
  · rw [← Matrix.trace_toLin'_eq, ← hf, htr]
  · intro h0
    have hs : Subsingleton (LinearMap.range f) := (Module.finrank_eq_zero_iff_of_free O _).mp h0
    have hbot : LinearMap.range f = ⊥ := Submodule.subsingleton_iff_eq_bot.mp hs
    rw [LinearMap.range_eq_bot, hf] at hbot
    exact Matrix.toLin'.injective (by rw [hbot, map_zero])
end GlobalTheory.CompanionTheory.IdemTrace
