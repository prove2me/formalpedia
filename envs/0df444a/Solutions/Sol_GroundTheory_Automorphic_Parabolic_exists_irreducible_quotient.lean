-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_irreducible_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:25.750973+00:00
-- url     : https://prove2.me/submissions/027cfebc-2507-4d79-afa3-47ee366892f3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_mem_subset_of_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution [Nontrivial U] (S : Finset U)
    (hS : Submodule.span ℂ {x | ∃ g, ∃ s ∈ S, x = τ g s} = ⊤) :
    ∃ (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)),
      (Representation.quotient τ Y hY).IsIrreducible := by
  classical
  let P : Set (Submodule ℂ U) := {Y | (∀ g, Y ≤ Y.comap (τ g)) ∧ ¬ ((S : Set U) ⊆ Y)}

  have htop : ∀ Z : Submodule ℂ U, (∀ g, Z ≤ Z.comap (τ g)) → (S : Set U) ⊆ Z → Z = ⊤ := by
    intro Z hZ hSZ
    rw [eq_top_iff, ← hS]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, s, hs, rfl⟩
    exact hZ g (hSZ hs)
  have hbot : (⊥ : Submodule ℂ U) ∈ P := by
    refine ⟨fun g => bot_le, fun h => ?_⟩
    have := htop ⊥ (fun g => bot_le) h
    exact bot_ne_top this
  obtain ⟨Y, -, hYmax⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    refine ⟨sSup c, ⟨fun g x hx => ?_, fun hsub => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).1 hx
      exact (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).2 ⟨Z, hZ, (hcP hZ).1 g hxZ⟩
    · obtain ⟨Z, hZ, hSZ⟩ := exists_mem_subset_of_chain hc hy S fun s hs =>
        (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).1 (hsub hs)
      exact (hcP hZ).2 fun s hs => hSZ s hs) ⊥ hbot
  obtain ⟨⟨hYs, hYS⟩, hYm⟩ := hYmax
  refine ⟨Y, hYs, ?_⟩
  have hYtop : Y ≠ ⊤ := fun h => hYS (by rw [h]; exact fun _ _ => Submodule.mem_top)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hYtop ?_⟩, eq_bot_or_eq_top := fun X => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    rw [eq_top_iff]
    intro x _
    have hx : (Submodule.Quotient.mk x : U ⧸ Y) ∈ (⊤ : Subrepresentation (Representation.quotient τ Y hYs)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hx
    exact (Submodule.Quotient.mk_eq_zero Y).1 hx
  · let Z : Submodule ℂ U := X.toSubmodule.comap Y.mkQ
    have hZs : ∀ g, Z ≤ Z.comap (τ g) := by
      intro g x hx
      show Submodule.Quotient.mk (τ g x) ∈ X.toSubmodule
      have := X.apply_mem_toSubmodule g hx
      exact this
    have hYZ : Y ≤ Z := by
      intro x hx
      show Submodule.Quotient.mk x ∈ X.toSubmodule
      rw [(Submodule.Quotient.mk_eq_zero Y).2 hx]
      exact X.toSubmodule.zero_mem
    by_cases hSZ : (S : Set U) ⊆ Z
    · right
      have hZt := htop Z hZs hSZ
      apply Subrepresentation.ext
      show X.toSubmodule = ⊤
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Y x
      have hu : u ∈ Z := by rw [hZt]; exact Submodule.mem_top
      exact hu
    · left
      have hZY : Z ≤ Y := hYm ⟨hZs, hSZ⟩ hYZ
      apply Subrepresentation.ext
      show X.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Y x
      rw [Submodule.mem_bot]
      exact (Submodule.Quotient.mk_eq_zero Y).2 (hZY hx)
end GroundTheory.Automorphic.Parabolic
