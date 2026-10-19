-- Prove2me | solution 1 for OAI.SpinAngle.normalized_board_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:30:23.287016+00:00
-- url     : https://prove2.me/submissions/96a36fa4-9278-4deb-a208-46affd0186f8

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/Core.lean:L4299-L4315
-- (upload_full_project.md Phase 4): solution for node OAI.SpinAngle.normalized_board_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core
import Theorems.Thm_OAI_SpinAngle_MatrixAnalysis_cell_trace_identity

-- ---- from OAI.RepresentationTheory.SpinAngle.Core ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
end TensorProduct
end Lean433TensorProductCompatibility

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace SpinAngle.Specht

variable {G : Type*} [contextInstance10_21 : Group G]
variable {E : Type*} [contextInstance11_21 : NormedAddCommGroup E] [contextInstance11_44 : InnerProductSpace ℂ E]

variable [contextInstance32_9 : FiniteDimensional ℂ E]

end SpinAngle.Specht

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance135_23 : Fintype ι] [contextInstance135_35 : DecidableEq ι] [contextInstance135_51 : Fintype n] [contextInstance135_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.Specht
open scoped Classical
variable {G : Type*} [contextInstance243_21 : Group G]
namespace PermutationSpace
open scoped Classical

variable {X : Type*} [contextInstance247_21 : Fintype X] [contextInstance247_33 : MulAction G X]

variable {H : Type*} [contextInstance278_21 : Group H] [contextInstance278_31 : Fintype H]

end PermutationSpace
variable {α : Type*} [contextInstance389_21 : Fintype α]

end SpinAngle.Specht

namespace SpinAngle.Young

end SpinAngle.Young

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι n : Type*} [contextInstance532_23 : Fintype ι] [contextInstance532_35 : DecidableEq ι] [contextInstance532_51 : Fintype n] [contextInstance532_63 : DecidableEq n]

variable (D : YoungDiagram) (q : ℕ)
variable (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.Specht.PermutationSpace
open scoped Classical
variable {G H X : Type*} [contextInstance635_25 : Group G] [contextInstance635_35 : Group H] [contextInstance635_45 : Fintype H] [contextInstance635_57 : Fintype X] [contextInstance635_69 : MulAction G X]
end SpinAngle.Specht.PermutationSpace

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable {ι : Type*} [contextInstance741_21 : Fintype ι] [contextInstance741_33 : DecidableEq ι] {q : ℕ}

variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

namespace SpinAngle.TensorRep
open scoped Classical
variable {ι κ n : Type*} [contextInstance868_25 : Fintype ι] [contextInstance868_37 : DecidableEq ι] [contextInstance868_53 : Fintype κ] [contextInstance868_65 : DecidableEq κ]
  [contextInstance869_2 : Fintype n] [contextInstance869_14 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.TensorRep
open SpinAngle.Specht
variable {ι n : Type*} [contextInstance980_23 : Fintype ι] [contextInstance980_35 : DecidableEq ι] [contextInstance980_51 : Fintype n] [contextInstance980_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped Matrix ComplexOrder
namespace SpinAngle.SortedSpectrum
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.IsHermitian)

end SpinAngle.SortedSpectrum

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix InnerProductSpace
open SpinAngle.Specht SpinAngle.Young Module
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace BigOperators
namespace SpinAngle.ExternalTensor
open Module
variable {E F : Type*} [contextInstance1195_23 : NormedAddCommGroup E] [contextInstance1195_46 : InnerProductSpace ℂ E]
  [contextInstance1196_2 : NormedAddCommGroup F] [contextInstance1196_25 : InnerProductSpace ℂ F]
  [contextInstance1197_2 : FiniteDimensional ℂ E] [contextInstance1197_26 : FiniteDimensional ℂ F]
variable {G H : Type*} [contextInstance1198_23 : Group G] [contextInstance1198_33 : Group H]

end SpinAngle.ExternalTensor

noncomputable section
open scoped BigOperators ComplexConjugate
namespace SpinAngle.TorusNaturality
open Module
variable {n X Y E F : Type*} [contextInstance1400_29 : Fintype n] [contextInstance1400_41 : Fintype X] [contextInstance1400_53 : Fintype Y]
  [contextInstance1401_2 : AddCommGroup E] [contextInstance1401_19 : Module ℂ E] [contextInstance1401_32 : AddCommGroup F] [contextInstance1401_49 : Module ℂ F]
variable (b : Basis X ℂ E) (c : Basis Y ℂ F)
  (w : X → n → ℕ) (v : Y → n → ℕ)
  (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
  (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
  (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y)

end SpinAngle.TorusNaturality

namespace SpinAngle.SignedTensor
open scoped Classical Matrix TensorProduct InnerProductSpace
open Module
variable {q : ℕ}
variable {ι κ τ : Type*} [contextInstance1517_25 : Fintype ι] [contextInstance1517_37 : DecidableEq ι] [contextInstance1517_53 : Fintype κ] [contextInstance1517_65 : DecidableEq κ]
  [contextInstance1518_2 : Fintype τ] [contextInstance1518_14 : DecidableEq τ]

end SpinAngle.SignedTensor

noncomputable section
open scoped InnerProductSpace
namespace SpinAngle.UnitaryNaturality
variable {G : Type*} [contextInstance1640_21 : Group G]
variable {E F : Type*} [contextInstance1641_23 : NormedAddCommGroup E] [contextInstance1641_46 : InnerProductSpace ℂ E]
  [contextInstance1642_2 : NormedAddCommGroup F] [contextInstance1642_25 : InnerProductSpace ℂ F]
  [contextInstance1643_2 : FiniteDimensional ℂ E] [contextInstance1643_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ)
  (hσ : ∀ g x y, ⟪σ g x,σ g y⟫_ℂ = ⟪x,y⟫_ℂ)

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)
end SpinAngle.PolynomialCarrier

namespace SpinAngle.ExternalTensor
open scoped TensorProduct
variable {G H : Type*} [contextInstance1802_23 : Group G] [contextInstance1802_33 : Group H] [contextInstance1802_43 : TopologicalSpace G] [contextInstance1802_64 : TopologicalSpace H]
variable {E F : Type*} [contextInstance1803_23 : NormedAddCommGroup E] [contextInstance1803_46 : InnerProductSpace ℂ E]
  [contextInstance1804_2 : NormedAddCommGroup F] [contextInstance1804_25 : InnerProductSpace ℂ F]
  [contextInstance1805_2 : FiniteDimensional ℂ E] [contextInstance1805_26 : FiniteDimensional ℂ F]
end SpinAngle.ExternalTensor

namespace SpinAngle.SignedTensor
variable {q : ℕ} {τ : Type*} [contextInstance1828_29 : Fintype τ] [contextInstance1828_41 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
end SpinAngle.SignedCarrier

namespace SpinAngle.TensorRep
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance1859_23 : Fintype ι] [contextInstance1859_35 : DecidableEq ι] [contextInstance1859_51 : Fintype n] [contextInstance1859_63 : DecidableEq n]
end SpinAngle.TensorRep

namespace SpinAngle.PolynomialCarrier
open scoped Classical InnerProductSpace
open SpinAngle.Young SpinAngle.Specht
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
namespace SpinAngle.TensorPositive
variable {E F : Type*} [contextInstance1947_23 : NormedAddCommGroup E] [contextInstance1947_46 : InnerProductSpace ℂ E]
  [contextInstance1948_2 : NormedAddCommGroup F] [contextInstance1948_25 : InnerProductSpace ℂ F]
  [contextInstance1949_2 : FiniteDimensional ℂ E] [contextInstance1949_26 : FiniteDimensional ℂ F]

end SpinAngle.TensorPositive

noncomputable section
open scoped BigOperators
namespace SpinAngle.EntropyMonomial
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

end SpinAngle.EntropyMonomial

noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators
namespace SpinAngle.PositiveTrace
variable {E : Type*} [contextInstance2090_21 : NormedAddCommGroup E] [contextInstance2090_44 : InnerProductSpace ℂ E]
  [contextInstance2091_2 : FiniteDimensional ℂ E]

end SpinAngle.PositiveTrace

noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
namespace SpinAngle.Isotypic
variable {G : Type*} [contextInstance2131_21 : Group G]
variable {E F : Type*} [contextInstance2132_23 : NormedAddCommGroup E] [contextInstance2132_46 : InnerProductSpace ℂ E]
  [contextInstance2133_2 : NormedAddCommGroup F] [contextInstance2133_25 : InnerProductSpace ℂ F]
  [contextInstance2134_2 : FiniteDimensional ℂ E] [contextInstance2134_26 : FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)

end SpinAngle.Isotypic

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

end SpinAngle.SignedCarrier

namespace SpinAngle.EntropyMonomial
open scoped BigOperators
variable {ι : Type*} [contextInstance2379_21 : Fintype ι] [contextInstance2379_33 : Nonempty ι]

end SpinAngle.EntropyMonomial

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance2407_21 : Fintype τ] [contextInstance2407_33 : DecidableEq τ]

end SpinAngle.SignedCarrier

noncomputable section
open scoped BigOperators
namespace SpinAngle.DenseLU

end SpinAngle.DenseLU

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier
noncomputable section
open scoped BigOperators
namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable (σ : Type*) [contextInstance2689_21 : Fintype σ] [contextInstance2689_33 : DecidableEq σ] (p : ℕ)

variable {q : ℕ}
end SpinAngle.PolyDimension

namespace SpinAngle.PolyDimension
open MvPolynomial Module
variable {σ X : Type*} [contextInstance2737_23 : Fintype σ] [contextInstance2737_35 : DecidableEq σ] [contextInstance2737_51 : Fintype X] (p : ℕ)

end SpinAngle.PolyDimension

namespace SpinAngle.PolynomialCarrier
open scoped Classical Matrix
open SpinAngle.Specht SpinAngle.Young PolyDimension MvPolynomial
variable (D : YoungDiagram) (q : ℕ) (hq : D.colLen 0 ≤ q)

end SpinAngle.PolynomialCarrier

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
namespace SpinAngle.CompactTwirl

variable {G : Type*} [contextInstance2861_21 : Group G] [contextInstance2861_31 : TopologicalSpace G] [contextInstance2861_52 : IsTopologicalGroup G]
  [contextInstance2862_2 : CompactSpace G] [contextInstance2862_19 : MeasurableSpace G] [contextInstance2862_39 : BorelSpace G]

variable {A : Type*} [contextInstance2877_21 : NormedRing A] [contextInstance2877_36 : NormedAlgebra ℝ A] [contextInstance2877_56 : CompleteSpace A]

section Positivity
variable [contextInstance2919_9 : PartialOrder A] [contextInstance2919_26 : IsOrderedAddMonoid A] [contextInstance2919_49 : StarRing A] [contextInstance2919_62 : StarOrderedRing A]
  [contextInstance2920_2 : ClosedIciTopology A] [contextInstance2920_24 : IsOrderedModule ℝ A]

end Positivity

end SpinAngle.CompactTwirl

namespace SpinAngle
open scoped Matrix.Norms.L2Operator

end SpinAngle

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance2949_21 : Group G] [contextInstance2949_31 : TopologicalSpace G] [contextInstance2949_52 : IsTopologicalGroup G]
  [contextInstance2950_2 : CompactSpace G] [contextInstance2950_19 : MeasurableSpace G] [contextInstance2950_39 : BorelSpace G]
variable {E : Type*} [contextInstance2951_21 : NormedAddCommGroup E] [contextInstance2951_44 : InnerProductSpace ℂ E]
  [contextInstance2952_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3008_21 : Group G] [contextInstance3008_31 : TopologicalSpace G] [contextInstance3008_52 : IsTopologicalGroup G]
  [contextInstance3009_2 : CompactSpace G] [contextInstance3009_19 : MeasurableSpace G] [contextInstance3009_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3010_23 : NormedAddCommGroup E] [contextInstance3010_46 : InnerProductSpace ℂ E]
  [contextInstance3011_2 : NormedAddCommGroup F] [contextInstance3011_25 : InnerProductSpace ℂ F]
  [contextInstance3012_2 : FiniteDimensional ℂ E] [contextInstance3012_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3043_21 : CStarAlgebra A] [contextInstance3043_38 : PartialOrder A] [contextInstance3043_55 : StarOrderedRing A]
  [contextInstance3044_2 : NonnegSpectrumClass ℝ A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.CompactTwirl
open scoped InnerProductSpace ComplexOrder
variable {G : Type*} [contextInstance3062_21 : Group G] [contextInstance3062_31 : TopologicalSpace G] [contextInstance3062_52 : IsTopologicalGroup G]
  [contextInstance3063_2 : CompactSpace G] [contextInstance3063_19 : MeasurableSpace G] [contextInstance3063_39 : BorelSpace G]
variable {E F : Type*} [contextInstance3064_23 : NormedAddCommGroup E] [contextInstance3064_46 : InnerProductSpace ℂ E]
  [contextInstance3065_2 : NormedAddCommGroup F] [contextInstance3065_25 : InnerProductSpace ℂ F]
  [contextInstance3066_2 : FiniteDimensional ℂ E] [contextInstance3066_26 : FiniteDimensional ℂ F]

end SpinAngle.CompactTwirl

noncomputable section
open scoped BigOperators
open Set
namespace SpinAngle.CompactMixture
variable {E : Type*} [contextInstance3119_21 : NormedAddCommGroup E] [contextInstance3119_44 : NormedSpace ℝ E] [contextInstance3119_62 : FiniteDimensional ℝ E]

end SpinAngle.CompactMixture

namespace SpinAngle.CompactTwirl
variable {G : Type*} [contextInstance3168_21 : Group G] [contextInstance3168_31 : TopologicalSpace G] [contextInstance3168_52 : IsTopologicalGroup G]
  [contextInstance3169_2 : CompactSpace G] [contextInstance3169_19 : MeasurableSpace G] [contextInstance3169_39 : BorelSpace G]
variable {E : Type*} [contextInstance3170_21 : NormedAddCommGroup E] [contextInstance3170_44 : InnerProductSpace ℂ E]
  [contextInstance3171_2 : FiniteDimensional ℂ E]

end SpinAngle.CompactTwirl

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}

variable {τ : Type*} [contextInstance3254_21 : Fintype τ] [contextInstance3254_33 : DecidableEq τ]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedTensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
variable [contextInstance3273_9 : Nonempty (Fin q)]
end SpinAngle.SignedTensor

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3283_21 : Fintype τ] [contextInstance3283_33 : DecidableEq τ]

variable [contextInstance3288_9 : Nonempty (Fin q)]
end SpinAngle.SignedCarrier

noncomputable section
namespace SpinAngle.ProjectionOrder
variable {A : Type*} [contextInstance3309_21 : CStarAlgebra A] [contextInstance3309_38 : PartialOrder A] [contextInstance3309_55 : StarOrderedRing A]

end SpinAngle.ProjectionOrder

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3325_21 : Fintype n] [contextInstance3325_33 : DecidableEq n]
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor CompactTwirl
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3337_21 : Fintype τ] [contextInstance3337_33 : DecidableEq τ] [contextInstance3337_49 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.MatrixBridge
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3364_21 : Fintype n] [contextInstance3364_33 : DecidableEq n]
local notation "Φ" => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
end SpinAngle.MatrixBridge

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open SpinAngle.Young SpinAngle.Specht SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)
variable {τ : Type*} [contextInstance3392_21 : Fintype τ] [contextInstance3392_33 : DecidableEq τ]

variable [contextInstance3441_9 : Nonempty (Fin q)]

end SpinAngle.SignedCarrier

namespace SpinAngle.SignedTensor
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ}
variable {J : Type*} [contextInstance3487_21 : Fintype J]

end SpinAngle.SignedTensor

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpinAngle.MatrixAnalysis
variable {n : Type*} [contextInstance3521_21 : Fintype n] [contextInstance3521_33 : DecidableEq n]
lemma root_selfAdjoint (a : Mat n) : IsSelfAdjoint (root a) :=
  cfc_predicate _ _
lemma support_selfAdjoint (a : Mat n) : IsSelfAdjoint (support a) :=
  cfc_predicate _ _

lemma root_mul_self (a : Mat n) (ha : 0 ≤ a) : root a * root a = a := by
  rw [root, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x hx
      exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg ha hx)
    _ = a := cfc_id' ℝ (ha := .of_nonneg ha)

lemma invRoot_mul_root (a : Mat n) (ha : 0 ≤ a) :
    invRoot a * root a = support a := by
  rw [invRoot, root, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (lt_of_le_of_ne (spectrum_nonneg_of_nonneg ha hx) (Ne.symm hx0)))
    simp [hx0, hs]

lemma support_isStarProjection (a : Mat n) : IsStarProjection (support a) := by
  refine ⟨?_, support_selfAdjoint a⟩
  change support a * support a = support a
  rw [support, ← cfc_mul _ _ _ (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)
    (Matrix.finite_real_spectrum (A := a) |>.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma root_commute {a b : Mat n} (h : Commute a b) : Commute (root a) b :=
  h.cfc_real _
lemma invRoot_commute {a b : Mat n} (h : Commute a b) : Commute (invRoot a) b :=
  h.cfc_real _
lemma norm_le_re_trace (a : Mat n) (ha : 0 ≤ a) : ‖a‖ ≤ (Matrix.trace a).re := by
  have hA := Matrix.nonneg_iff_posSemidef.mp ha
  rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  conv_lhs => rw [hA.isHermitian.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by
    exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i)).mpr
  intro i
  simp only [Function.comp_apply, RCLike.norm_ofReal,
    abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma norm_sq_le_re_trace_star_mul_self (a : Mat n) :
    ‖a‖ ^ 2 ≤ (Matrix.trace (star a * a)).re := by
  rw [sq, ← CStarRing.norm_star_mul_self]
  exact norm_le_re_trace _ (star_mul_self_nonneg _)

lemma invRoot_mul_self_mul_invRoot (a : Mat n) (ha : 0 ≤ a) :
    invRoot a * a * invRoot a = support a := by
  have hc : Commute (invRoot a) a := invRoot_commute (Commute.refl a)
  have hr : Commute (root a) (invRoot a) := root_commute hc.symm
  calc
    invRoot a * a * invRoot a = invRoot a * (root a * root a) * invRoot a :=
      congrArg (fun x => invRoot a * x * invRoot a) (root_mul_self a ha).symm
    _ = (invRoot a * root a) * (root a * invRoot a) := by simp only [mul_assoc]
    _ = support a * support a := by rw [hr.eq, invRoot_mul_root a ha]
    _ = support a := (support_isStarProjection a).isIdempotentElem.eq

lemma cell_trace_nonneg (a b c : Mat n) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    0 ≤ (invRoot b * a * invRoot b * c).trace := by
  rw [← cell_trace_identity a b c ha hc]
  exact (Matrix.nonneg_iff_posSemidef.mp (star_mul_self_nonneg _)).trace_nonneg

lemma re_trace_nonneg
    {n : Type*}
    [contextInstance3521_21 : Fintype n]
    [DecidableEq n] (a : Mat n) (ha : 0 ≤ a) : 0 ≤ a.trace.re :=
  (Complex.nonneg_iff.mp ((Matrix.nonneg_iff_posSemidef.mp ha).trace_nonneg)).1

lemma re_trace_mono {a b : Mat n} (hab : a ≤ b) : a.trace.re ≤ b.trace.re := by
  have h := re_trace_nonneg (b - a) (sub_nonneg.mpr hab)
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

lemma re_trace_projection_mul_le (q b : Mat n) (hq : IsStarProjection q) (hb : 0 ≤ b) :
    (q * b).trace.re ≤ b.trace.re := by
  have h := re_trace_mono (star_left_conjugate_le_conjugate hq.le_one (root b))
  rw [mul_one, (root_selfAdjoint b).star_eq, root_mul_self b hb] at h
  rw [Matrix.trace_mul_comm (root b * q) (root b), ← mul_assoc,
    root_mul_self b hb, Matrix.trace_mul_comm b q] at h
  exact h

end SpinAngle.MatrixAnalysis

namespace SpinAngle.TensorMatrix
open SpinAngle.MatrixAnalysis
variable {ι n : Type*} [contextInstance3707_23 : Fintype ι] [contextInstance3707_35 : DecidableEq ι] [contextInstance3707_51 : Fintype n] [contextInstance3707_63 : DecidableEq n]

lemma tensor_star
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [DecidableEq ι]
    [Fintype n]
    [DecidableEq n] (a : ι → Mat n) :
    tensor (fun i => star (a i)) = star (tensor a) := by
  ext x y
  simp [tensor, Matrix.star_apply]

lemma tensor_mul
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [contextInstance3707_35 : DecidableEq ι]
    [contextInstance3707_51 : Fintype n]
    [DecidableEq n] (a b : ι → Mat n) :
    tensor (fun i => a i * b i) = tensor a * tensor b := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  symm
  simpa using (Finset.sum_prod_piFinset (ι := ι) Finset.univ
    (fun i j => a i (x i) j * b i j (y i)))

lemma tensor_trace
    {ι : Type*} {n : Type*}
    [contextInstance3707_23 : Fintype ι]
    [contextInstance3707_35 : DecidableEq ι]
    [contextInstance3707_51 : Fintype n]
    [DecidableEq n] (a : ι → Mat n) :
    (tensor a).trace = ∏ i, (a i).trace := by
  simp only [Matrix.trace, Matrix.diag, tensor]
  simpa using (Finset.sum_prod_piFinset (ι := ι) Finset.univ
    (fun i j => a i j j))

lemma tensor_norm_sq_le_trace_product (a : ι → Mat n) :
    ‖tensor a‖ ^ 2 ≤ (∏ i, (star (a i) * a i).trace).re := by
  have h := norm_sq_le_re_trace_star_mul_self (tensor a)
  rw [← tensor_star, ← tensor_mul, tensor_trace] at h
  exact h

lemma tensor_norm_sq_le_re_trace_product (a : ι → Mat n) :
    ‖tensor a‖ ^ 2 ≤ ∏ i, (star (a i) * a i).trace.re := by
  have hreal (i : ι) : (star (a i) * a i).trace = ((star (a i) * a i).trace.re : ℂ) :=
    Complex.eq_re_of_ofReal_le (r := 0)
      (by exact (Matrix.nonneg_iff_posSemidef.mp (star_mul_self_nonneg _)).trace_nonneg)
  calc
    _ ≤ (∏ i, (star (a i) * a i).trace).re := tensor_norm_sq_le_trace_product a
    _ = (∏ i, ((star (a i) * a i).trace.re : ℂ)).re :=
      congrArg Complex.re (Finset.prod_congr rfl fun i _ => hreal i)
    _ = _ := by rw [← Complex.ofReal_prod, Complex.ofReal_re]

lemma tensor_cell_norm_sq_le_product (a b c : ι → Mat n)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) :
    ‖tensor (fun i => root (a i) * invRoot (b i) * root (c i))‖ ^ 2 ≤
      ∏ i, (invRoot (b i) * a i * invRoot (b i) * c i).trace.re := by
  have h := tensor_norm_sq_le_re_trace_product (fun i => root (a i) * invRoot (b i) * root (c i))
  simpa only [cell_trace_identity _ _ _ (ha _) (hc _)] using h

end SpinAngle.TensorMatrix

noncomputable section
open scoped BigOperators
namespace SpinAngle

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]

lemma retained_product_le
    {ι : Type*}
    [contextInstance3841_21 : Fintype ι]
    [DecidableEq ι] (t : Finset ι) (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hs : ∑ i, z i ≤ Fintype.card ι) :
    ∏ i ∈ t, z i ≤ ((Fintype.card ι : ℝ) / t.card) ^ t.card := by
  by_cases ht : t.Nonempty
  · have hkR : 0 < (t.card : ℝ) := by exact_mod_cast ht.card_pos
    have hmR : 0 < (Fintype.card ι : ℝ) :=
      hkR.trans_le (by exact_mod_cast Finset.card_le_univ t)
    let c : ℝ := Fintype.card ι / t.card
    have hc : 0 < c := div_pos hmR hkR
    have hsum : ∑ i ∈ t, z i ≤ Fintype.card ι :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro i _ _; exact hz i)).trans hs
    have hnorm : ∑ i ∈ t, z i / c ≤ t.card := by
      rw [← Finset.sum_div]
      apply (div_le_iff₀ hc).mpr
      dsimp [c]
      rwa [mul_div_cancel₀ _ hkR.ne']
    have hn : ∏ i ∈ t, z i / c ≤ 1 := calc
      _ ≤ ∏ i ∈ t, Real.exp (z i / c - 1) :=
        Finset.prod_le_prod₀ (fun i _ => div_nonneg (hz i) hc.le) fun i _ => by
          have h := Real.add_one_le_exp (z i / c - 1)
          linarith
      _ = Real.exp (∑ i ∈ t, (z i / c - 1)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_sub_distrib]
        simpa using sub_nonpos.mpr hnorm
      _ = 1 := Real.exp_zero
    rw [Finset.prod_div_distrib, Finset.prod_const] at hn
    exact (div_le_one (pow_pos hc _)).mp hn
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [he]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]

lemma occupiedRow_card_le
    {R : Type*} {C : Type*}
    [Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (i : R) :
    (occupiedRow W i).card ≤ Fintype.card C := Finset.card_le_univ _

lemma retained_factor_eq_missingCellFactor (W : Finset (R × C)) (i : R) :
    ((Fintype.card C : ℝ) / (occupiedRow W i).card) ^ (occupiedRow W i).card =
      missingCellFactor (Fintype.card C) (missingInRow W i) := by
  have hc := occupiedRow_card_le W i
  unfold missingInRow missingCellFactor
  rw [Nat.sub_sub_self hc]
  split_ifs with h
  · rfl
  · have hk : (occupiedRow W i).card = 0 := by omega
    simp [hk]

lemma prod_occupiedRow
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    {R : Type*} {C : Type*}
    [contextInstance3877_23 : Fintype R]
    [contextInstance3877_35 : DecidableEq R]
    [contextInstance3877_51 : Fintype C]
    [contextInstance3877_63 : DecidableEq C] (W : Finset (R × C)) (z : R → C → ℝ) :
    (∏ i, ∏ j ∈ occupiedRow W i, z i j) = ∏ x ∈ W, z x.1 x.2 := by
  simp only [occupiedRow, Finset.prod_filter]
  rw [← Finset.prod_product (f := fun x : R × C => if x ∈ W then z x.1 x.2 else 1)]
  simp only [Finset.univ_product_univ, ← Finset.prod_filter]
  congr 1
  ext x
  simp

lemma board_product_le (W : Finset (R × C)) (z : R → C → ℝ)
    (hz : ∀ i j, 0 ≤ z i j) (hs : ∀ i, ∑ j, z i j ≤ Fintype.card C) :
    (∏ x ∈ W, z x.1 x.2) ≤
      missingCellProductFactor (Fintype.card C) (missingInRow W) := by
  rw [← prod_occupiedRow (ι := R) W z]
  unfold missingCellProductFactor
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.prod_nonneg fun j _ => hz i j
  · intro i _
    rw [← retained_factor_eq_missingCellFactor]
    exact retained_product_le (occupiedRow W i) (z i) (hz i) (hs i)

end SpinAngle

namespace SpinAngle.MatrixAnalysis
variable {n C : Type*} [contextInstance3931_23 : Fintype n] [contextInstance3931_35 : DecidableEq n] [contextInstance3931_51 : Fintype C] [contextInstance3931_63 : DecidableEq C]

lemma average_nonneg
    {n : Type*} {C : Type*}
    [contextInstance3931_23 : Fintype n]
    [contextInstance3931_35 : DecidableEq n]
    [contextInstance3931_51 : Fintype C]
    [DecidableEq C] (r : C → Density n) : 0 ≤ average r :=
  smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun j _ => (r j).nonneg)

lemma sum_eq_smul_average
    {n : Type*} {C : Type*}
    [contextInstance3931_23 : Fintype n]
    [contextInstance3931_35 : DecidableEq n]
    [contextInstance3931_51 : Fintype C]
    [DecidableEq C] [Nonempty C] (r : C → Density n) :
    (∑ j, (r j).matrix) = (Fintype.card C : ℝ) • average r := by
  unfold average
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := C)), one_smul]

lemma support_cell_trace_sum [Nonempty C] (r : C → Density n) (s : Density n) :
    ∑ j, (invRoot (average r) * (r j).matrix * invRoot (average r) * s.matrix).trace.re ≤
      Fintype.card C := by
  have he : (∑ j, invRoot (average r) * (r j).matrix * invRoot (average r) * s.matrix) =
      (Fintype.card C : ℝ) • (support (average r) * s.matrix) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_eq_smul_average r, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      invRoot_mul_self_mul_invRoot _ (average_nonneg r)]
  have ht := congrArg (fun a : Mat n => a.trace.re) he
  simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at ht
  rw [ht]
  have h := re_trace_projection_mul_le (support (average r)) s.matrix
    (support_isStarProjection _) s.nonneg
  rw [s.trace_eq_one, Complex.one_re] at h
  simpa using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card C))

end SpinAngle.MatrixAnalysis

namespace SpinAngle
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]

theorem normalized_board_bound (W : Finset (R × C))
    (r : C → Density n) (s : R → Density n) :
    ‖tensor (fun w : W => root (r w.val.2).matrix *
      invRoot (average r) * root (s w.val.1).matrix)‖ ^ 2 ≤
        missingCellProductFactor (Fintype.card C) (missingInRow W) := by
  let z : R → C → ℝ := fun i j =>
    (invRoot (average r) * (r j).matrix * invRoot (average r) * (s i).matrix).trace.re
  have hz : ∀ i j, 0 ≤ z i j := fun i j =>
    (Complex.nonneg_iff.mp (cell_trace_nonneg _ _ _ (r j).nonneg (s i).nonneg)).1
  have hs : ∀ i, ∑ j, z i j ≤ Fintype.card C := fun i => support_cell_trace_sum r (s i)
  calc
    _ ≤ ∏ w : W, z w.val.1 w.val.2 :=
      tensor_cell_norm_sq_le_product _ _ _ (fun w => (r w.val.2).nonneg)
        (fun w => (s w.val.1).nonneg)
    _ = ∏ w ∈ W, z w.1 w.2 :=
      (Finset.prod_subtype W (by intro w; rfl) (fun w => z w.1 w.2)).symm
    _ ≤ _ := board_product_le W z hz hs

end SpinAngle

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SpinAngle.DependentTensor
variable {ι : Type*} [contextInstance4012_21 : Fintype ι] [contextInstance4012_33 : DecidableEq ι]
variable {ν : ι → Type*} [contextInstance4013_25 : ∀ i, Fintype (ν i)] [contextInstance4013_46 : ∀ i, DecidableEq (ν i)]

end SpinAngle.DependentTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4107_25 : Fintype τ] [contextInstance4107_37 : DecidableEq τ] [contextInstance4107_53 : Fintype J] [contextInstance4107_65 : DecidableEq J]
  [contextInstance4108_2 : Fintype n] [contextInstance4108_14 : DecidableEq n]
variable (f : τ → J)

end SpinAngle.BlockTensor

namespace SpinAngle.BlockTensor
open DependentTensor
variable {τ J n : Type*} [contextInstance4180_25 : Fintype τ] [contextInstance4180_37 : DecidableEq τ] [contextInstance4180_53 : Fintype J] [contextInstance4180_65 : DecidableEq J]
  [contextInstance4181_2 : Fintype n] [contextInstance4181_14 : DecidableEq n]
variable (f : τ → J)

end SpinAngle.BlockTensor

namespace SpinAngle.TensorMatrix
open MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {ι n : Type*} [contextInstance4214_23 : Fintype ι] [contextInstance4214_35 : DecidableEq ι] [contextInstance4214_51 : Fintype n] [contextInstance4214_63 : DecidableEq n]

end SpinAngle.TensorMatrix

namespace SpinAngle
open scoped BigOperators
variable {R C : Type*} [contextInstance4250_23 : Fintype R] [contextInstance4250_35 : DecidableEq R] [contextInstance4250_51 : Fintype C] [contextInstance4250_63 : DecidableEq C]

end SpinAngle

namespace SpinAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young

namespace TypeLabel
variable {q : ℕ}
end TypeLabel

namespace EvenDensity
variable {q : ℕ}
variable {J : Type*} [contextInstance4345_21 : Fintype J] [contextInstance4345_33 : Nonempty J]
end EvenDensity

namespace TypeLabel
variable {q : ℕ}
variable {τ : Type*} [contextInstance4358_21 : Fintype τ] [contextInstance4358_33 : DecidableEq τ]
variable [contextInstance4367_9 : Nonempty (Fin q)]
end TypeLabel

namespace TypeBlocks
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]

variable [contextInstance4410_9 : Nonempty (Fin q)]

end TypeBlocks
end SpinAngle

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SpinAngle
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open MatrixAnalysis TensorMatrix


theorem solution : type_of% @_root_.OAI.SpinAngle.normalized_board_bound := @_root_.OAI.SpinAngle.normalized_board_bound
