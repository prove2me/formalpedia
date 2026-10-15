-- Prove2me | solution 1 for OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:23:28.352978+00:00
-- url     : https://prove2.me/submissions/dc8a3c51-d9d6-4202-9352-31381328f4cf

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/LocalCanonical.lean:L64-L85
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical

-- ---- from OAI.AlgebraicGeometry.LogKodaira.LocalCanonical ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct

namespace ReverseLogKodaira.LocalCanonical

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

 
 
 
lemma span_wedges (n : ℕ) :
    Submodule.span A (Set.range fun a : Fin n → A =>
      exteriorPower.ιMulti A n fun i => KaehlerDifferential.D R A (a i)) = ⊤ := by
  have h := exteriorPower.ιMulti_span_of_span A n (KaehlerDifferential R A)
    (KaehlerDifferential.span_range_derivation R A)
  convert h using 2
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => KaehlerDifferential.D R A (a i), by
      rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : ∀ i, ∃ a, KaehlerDifferential.D R A a = v i :=
      fun i => hv ⟨i, rfl⟩
    choose a ha using hv'
    exact ⟨a, congrArg (exteriorPower.ιMulti A n) (funext ha)⟩

lemma exteriorPullback_wedge (n : ℕ) (a : Fin n → A) :
    exteriorPullback R A K n (exteriorPower.ιMulti A n
      fun i => KaehlerDifferential.D R A (a i)) =
      exteriorPower.ιMulti K n fun i =>
        KaehlerDifferential.D R K (algebraMap A K (a i)) := by
  simp [exteriorPullback, alternatingRestriction]
  rfl

 

theorem range_pluricanonicalPullback (n m : ℕ) :
    LinearMap.range (pluricanonicalPullback R A K n m) =
      Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
        PiTensorProduct.tprod K fun j => exteriorPower.ιMulti K n fun i =>
          KaehlerDifferential.D R K (algebraMap A K (a j i))) := by
  have ht : Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
      PiTensorProduct.tprod A fun j => exteriorPower.ιMulti A n fun i =>
        KaehlerDifferential.D R A (a j i)) = ⊤ :=
    PiTensorProduct.submodule_span_eq_top (R := A)
      (M := fun _ : Fin m => Canonical R A n) (γ := fun _ => Fin n → A)
      (g := fun {i} a => exteriorPower.ιMulti A n fun j => KaehlerDifferential.D R A (a j))
      (fun _ => span_wedges R A n)
  rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    simp [pluricanonicalPullback, exteriorPullback_wedge]
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨a, rfl⟩, ?_⟩
    simp [pluricanonicalPullback, exteriorPullback_wedge]

end ReverseLogKodaira.LocalCanonical

end
end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.LocalCanonical
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open scoped TensorProduct
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

theorem solution (n m : ℕ) :
    LinearMap.range (pluricanonicalPullback R A K n m) =
      Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
        PiTensorProduct.tprod K fun j => exteriorPower.ιMulti K n fun i =>
          KaehlerDifferential.D R K (algebraMap A K (a j i))) := by
  first
    | exact OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback n m
    | exact OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback R A K n m
    | exact OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback
    | (apply OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.LocalCanonical.range_pluricanonicalPullback <;> assumption)
