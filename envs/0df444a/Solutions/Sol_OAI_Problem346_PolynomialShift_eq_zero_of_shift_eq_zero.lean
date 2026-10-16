-- Prove2me | solution 1 for OAI.Problem346.PolynomialShift.eq_zero_of_shift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:41:03.017393+00:00
-- url     : https://prove2.me/submissions/472b08f2-927e-4e1e-ad36-63113793ac63

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/BlockInjectivity.lean:L16-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.PolynomialShift.eq_zero_of_shift_eq_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Theorems.Thm_OAI_Problem346_derivation_eq_zero_of_positive_weight

-- ---- from OAI.RepresentationTheory.FoulkesHowe.BlockWeight ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346
namespace PolynomialWeights

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

/-- Euler's identity, expressed using a bundled derivation. -/
theorem weightedEuler_of_homogeneous (w : σ → ℕ) {n : ℕ}
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w n) :
    weightedEuler w f = n • f := by
  rw [weightedEuler_apply]
  exact hf.sum_weight_X_mul_pderiv

/-- Any derivation with the prescribed diagonal action on generators is Euler. -/
theorem derivation_eq_weightedEuler (w : σ → ℕ)
    (N : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hN : ∀ i, N (X i) = w i • X i) : N = weightedEuler w := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [hN, weightedEuler_X]

/-- A homogeneous polynomial is an eigenvector for its weighted Euler derivation. -/
theorem derivation_homogeneous_eigenvalue (w : σ → ℕ)
    (N : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hN : ∀ i, N (X i) = w i • X i)
    {n : ℕ} {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w n) :
    N f = n • f := by
  rw [derivation_eq_weightedEuler w N hN]
  exact weightedEuler_of_homogeneous w hf

section Blocks

variable {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq β]

theorem block_euler_eigenvalue (u : β)
    (N : Derivation R (MvPolynomial (β × ι) R) (MvPolynomial (β × ι) R))
    (hN : ∀ k i, N (X (k, i)) = if k = u then X (k, i) else 0)
    {n : ℕ} {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) :
    N f = n • f := by
  apply derivation_homogeneous_eigenvalue (blockWeight u) N _ hf
  rintro ⟨k, i⟩
  simp only [hN, blockWeight_apply]
  split_ifs <;> simp

/-- The difference of block counting operators has the difference of the block degrees
as eigenvalue. This is the weight used by the positive-weight shift lemma. -/
theorem block_difference_eigenvalue (u v : β)
    (Nu Nv : Derivation ℂ (MvPolynomial (β × ι) ℂ) (MvPolynomial (β × ι) ℂ))
    (hu : ∀ k i, Nu (X (k, i)) = if k = u then X (k, i) else 0)
    (hv : ∀ k i, Nv (X (k, i)) = if k = v then X (k, i) else 0)
    {p q : ℕ} {f : MvPolynomial (β × ι) ℂ}
    (hp : IsBlockHomogeneous u f p) (hq : IsBlockHomogeneous v f q) :
    (Nu - Nv) f = ((p : ℂ) - (q : ℂ)) • f := by
  change Nu f - Nv f = _
  rw [block_euler_eigenvalue u Nu hu hp, block_euler_eigenvalue v Nv hv hq]
  rw [sub_smul]
  simp only [Nat.cast_smul_eq_nsmul]

end Blocks

end PolynomialWeights
end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.PolynomialShift ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346
namespace PolynomialShift

variable {K B I : Type*} [CommRing K]

attribute [local instance] Classical.propDecidable

theorem commutator (src dst : B) (h : src ≠ dst) :
    ⁅derivation (K := K) (I := I) dst src, derivation (K := K) (I := I) src dst⁆ =
      derivation (K := K) (I := I) src src - derivation (K := K) (I := I) dst dst := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨block, i⟩
  by_cases hs : block = src <;> by_cases hd : block = dst <;>
    simp_all [Derivation.commutator_apply]

theorem weight_commutator (src dst : B) (h : src ≠ dst) :
    ⁅derivation (K := K) (I := I) src src - derivation (K := K) (I := I) dst dst,
      derivation (K := K) (I := I) dst src⁆ = (2 : K) • derivation (K := K) (I := I) dst src := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨block, i⟩
  by_cases hs : block = src <;> by_cases hd : block = dst <;>
    simp_all [Derivation.commutator_apply, two_smul]

end PolynomialShift
end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.BlockInjectivity ----
namespace OAI

noncomputable section

namespace Problem346
namespace PolynomialShift

open MvPolynomial PolynomialWeights

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]

/-- A polynomial block shift is injective in strictly positive source-minus-destination
weight. All other variable blocks are arbitrary spectators. -/
theorem eq_zero_of_shift_eq_zero (src dst : B) (hsd : src ≠ dst)
    {f : MvPolynomial (B × I) ℂ} {p q : ℕ} (hpq : q < p)
    (hp : IsBlockHomogeneous src f p) (hq : IsBlockHomogeneous dst f q)
    (hDf : shift src dst f = 0) : f = 0 := by
  refine derivation_eq_zero_of_positive_weight
    (derivation src dst) (derivation dst src)
    (derivation src src - derivation dst dst)
    (commutator src dst hsd) (weight_commutator src dst hsd) ?_
    f p q hpq ?_ hDf
  · rintro ⟨b, i⟩
    by_cases hb : b = dst
    · subst b
      simp [hsd]
    · simp [hb]
  · apply block_difference_eigenvalue src dst _ _ _ _ hp hq
    · intro b i
      by_cases hb : b = src
      · subst b; simp
      · simp [hb]
    · intro b i
      by_cases hb : b = dst
      · subst b; simp
      · simp [hb]

end PolynomialShift
end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.PolynomialShift
open MvPolynomial PolynomialWeights


theorem solution : type_of% @_root_.OAI.Problem346.PolynomialShift.eq_zero_of_shift_eq_zero := @_root_.OAI.Problem346.PolynomialShift.eq_zero_of_shift_eq_zero
