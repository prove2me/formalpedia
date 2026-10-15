-- Prove2me | solution 1 for OAI.BogomolovPop.transcendental_integer_character
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:35:05.373577+00:00
-- url     : https://prove2.me/submissions/b52a55b2-b180-475b-b6cb-ee33908ea9bb

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/PowerCompletion.lean:L595-L642
-- (upload_full_project.md Phase 4): solution for node OAI.BogomolovPop.transcendental_integer_character. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion

-- ---- from OAI.Algebra.BogomolovPop.PowerCompletion ----
namespace OAI

/-! Multiplicative power completions, integral characters and Frobenius endomorphisms. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

namespace PowerClass
variable {G H I : Type*} [CommGroup G] [CommGroup H] [CommGroup I]

end PowerClass

namespace PowerCompletion
variable {ell : ℕ} {G H I : Type*} [CommGroup G] [CommGroup H] [CommGroup I]

end PowerCompletion
end BogomolovPop

namespace BogomolovPop
noncomputable section

namespace PowerClass
variable {G : Type*} [CommGroup G]

end PowerClass

namespace PowerCompletion
variable {G : Type*} [CommGroup G] {ell : ℕ}

end PowerCompletion

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

lemma fractionTotalDegree_algebraMap (k ι : Type*) [Field k] (f : MvPolynomial ι k) :
    fractionTotalDegree k ι (algebraMap _ _ f) = polynomialTotalDegree k ι f := by
  exact Submonoid.LocalizationMap.lift_eq _ _ _

lemma fractionDegreeUnits_X (k ι : Type*) [Field k] (i : ι) :
    fractionDegreeUnits k ι (Units.mk0 (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) (MvPolynomial.X i))
      (by simp)) =
      Multiplicative.ofAdd (1 : ℤ) := by
  apply WithZero.coe_injective (α := Multiplicative ℤ)
  change (↑(WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ) _) : WithZero (Multiplicative ℤ)) = _
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  change fractionTotalDegree k ι (algebraMap _ _ (MvPolynomial.X i)) = _
  rw [fractionTotalDegree_algebraMap]
  simp [polynomialTotalDegree]

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

theorem transcendental_integer_character (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] (u : Fˣ)
    (hu : Transcendental k (u : F)) :
    ∃ d : Fˣ →* Multiplicative ℤ, d u ≠ 1 := by
  classical
  have hsingleton : AlgebraicIndepOn k id ({(u : F)} : Set F) := by
    apply algebraicIndependent_unique_type_iff.mpr
    simpa using hu
  obtain ⟨s, hs, ht⟩ := exists_isTranscendenceBasis_superset hsingleton
  let i : s := ⟨u, hs (Set.mem_singleton _)⟩
  let E := IntermediateField.adjoin k (Set.range ((↑) : s → F))
  have : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp k E F
  have : Algebra.IsAlgebraic E F := ht.isAlgebraic_field
  have : Module.Finite E F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let ξ : E ≃ₐ[k] FractionRing (MvPolynomial s k) := ht.1.aevalEquivField.symm
  let dE : Eˣ →* Multiplicative ℤ := (fractionDegreeUnits k s).comp
    (Units.map ξ.toRingHom.toMonoidHom)
  let v : Eˣ := Units.mk0 ⟨u, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
    (by exact fun h => u.ne_zero (congrArg (fun z : E => (z : F)) h))
  have hv : inclusionUnits E F v = u := by ext; rfl
  have hx : ξ (v : E) = algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) (MvPolynomial.X i) := by
    apply ξ.symm.injective
    rw [ξ.symm_apply_apply]
    apply Subtype.ext
    change (u : F) = ((ht.1.aevalEquivField (algebraMap _ _ (MvPolynomial.X i))) : F)
    rw [ht.1.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_X]
  have hdE : dE v = Multiplicative.ofAdd (1 : ℤ) := by
    change fractionDegreeUnits k s (Units.map ξ.toRingHom.toMonoidHom v) = _
    have he : Units.map ξ.toRingHom.toMonoidHom v = Units.mk0
        (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) (MvPolynomial.X i))
        (by simp) := Units.ext hx
    rw [he, fractionDegreeUnits_X]
  let d := dE.comp (normUnits E F)
  refine ⟨d, ?_⟩
  have hd : d u = Multiplicative.ofAdd (Module.finrank E F : ℤ) := by
    rw [← hv]
    have hn : normUnits E F (inclusionUnits E F v) = v ^ Module.finrank E F := by
      apply Units.ext
      exact Algebra.norm_algebraMap (v : E)
    change dE (normUnits E F _) = _
    rw [hn, map_pow, hdE]
    apply Multiplicative.toAdd.injective
    simp
  rw [hd]
  intro heq
  have hzero := congrArg Multiplicative.toAdd heq
  change (Module.finrank E F : ℤ) = 0 at hzero
  exact (Module.finrank_pos (R := E) (M := F)).ne' (Int.natCast_eq_zero.mp hzero)

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop
noncomputable section
namespace BogomolovPop

open Polynomial

end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.BogomolovPop
open scoped Topology

theorem solution (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] (u : Fˣ)
    (hu : Transcendental k (u : F)) :
    ∃ d : Fˣ →* Multiplicative ℤ, d u ≠ 1 := by
  first
    | exact OAI.BogomolovPop.transcendental_integer_character k F u hu
    | exact OAI.BogomolovPop.transcendental_integer_character
    | (apply OAI.BogomolovPop.transcendental_integer_character <;> assumption)
    | (intros; apply OAI.BogomolovPop.transcendental_integer_character <;> assumption)
