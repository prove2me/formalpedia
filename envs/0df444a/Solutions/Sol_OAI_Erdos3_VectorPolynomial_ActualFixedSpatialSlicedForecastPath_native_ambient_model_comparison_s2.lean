-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:17:49.315408+00:00
-- url     : https://prove2.me/submissions/1e886ccb-b7a8-42ab-a027-5518ef187230

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_native_ambient_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

theorem subtractConstant_neg_cancel {X R V : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    (c : V) (p : VectorPolynomial X R V) :
    subtractConstant (-c) (subtractConstant c p) = p := by
  simp [subtractConstant, monomial, TensorProduct.tmul_neg]

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] {periodCap coverCap : ℝ} {L : ℝ≥0}

@[simp] theorem eval_shiftConstant_neg_subtractConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.shiftConstant (fun j => -c j)).eval N
      (fun j => subtractConstant (c j) (poly j)) u = W.eval N poly u := by
  rw [eval_shiftConstant]
  simp only [subtractConstant_neg_cancel]

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv P : ℝ} {Lw Lv : ℝ≥0}

 theorem productUniform_exp_bounds
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv)
    (hP : 0 ≤ P) (hLw : (Lw : ℝ) ≤ Real.exp P) (hLv : (Lv : ℝ) ≤ Real.exp P)
    (hpw : pw ≤ Real.exp P) (hcw : cw ≤ Real.exp P)
    (hpv : pv ≤ Real.exp P) (hcv : cv ≤ Real.exp P) :
    ((Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
        Real.exp (2 * P + 1) ∧
      ((W.productUniform V).cover : ℝ) ≤ Real.exp (2 * P + 1) ∧
      ((W.productUniform V).modulus : ℝ) ≤ Real.exp (2 * P + 1) := by
  have hmax {c : ℝ} (hc : c ≤ Real.exp P) :
      ((max 1 (Real.toNNReal c) : ℝ≥0) : ℝ) ≤ Real.exp P := by
    simp only [NNReal.coe_max, NNReal.coe_one]
    exact max_le (Real.one_le_exp hP) (max_le hc (Real.exp_pos _).le)
  have hsum :
      ((Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
        2 * Real.exp (2 * P) := by
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
    have h1 := mul_le_mul hLw (hmax hcv)
      (NNReal.coe_nonneg (max 1 (Real.toNNReal cv))) (Real.exp_pos P).le
    have h2 := mul_le_mul hLv (hmax hcw)
      (NNReal.coe_nonneg (max 1 (Real.toNNReal cw))) (Real.exp_pos P).le
    have he : Real.exp P * Real.exp P = Real.exp (2 * P) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he] at h1 h2
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1; norm_num
  have hshift : 2 * Real.exp (2 * P) ≤ Real.exp (2 * P + 1) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmul {a b : ℕ} (ha : (a : ℝ) ≤ Real.exp P) (hb : (b : ℝ) ≤ Real.exp P) :
      ((a * b : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul ha hb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact ⟨hsum.trans hshift,
    hmul (W.cover_bound.trans hcw) (V.cover_bound.trans hcv),
    hmul (W.modulus_bound.trans hpw) (V.modulus_bound.trans hpv)⟩

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

attribute [instance] ActualForecastData.fintypeTerm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualForecastData
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ}
variable (data : ActualForecastData N originalpoly Pnative massLog capLog E)

theorem native_product_lipschitz_bound
    (_data : ActualForecastData N originalpoly Pnative massLog capLog E)
    {pw cw Ptest : ℝ} {Lw : ℝ≥0}
    (_W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (hPtest : 0 ≤ Ptest) (hLw : (Lw : ℝ) ≤ Real.exp Ptest)
    (hcw : cw ≤ Real.exp Ptest) :
    ((Lw * max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) +
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩ * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
      Real.exp (2 * max Ptest (3 * Pnative + 3) + 1) := by
  let P := max Ptest (3 * Pnative + 3)
  have hP : 0 ≤ P := hPtest.trans (le_max_left _ _)
  have ht : Real.exp Ptest ≤ Real.exp P := Real.exp_le_exp.mpr (le_max_left _ _)
  have hn : Real.exp (3 * Pnative + 3) ≤ Real.exp P :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  have hmax {c : ℝ} (hc : c ≤ Real.exp P) :
      ((max 1 (Real.toNNReal c) : ℝ≥0) : ℝ) ≤ Real.exp P := by
    simp only [NNReal.coe_max, NNReal.coe_one]
    exact max_le (Real.one_le_exp hP) (max_le hc (Real.exp_pos _).le)
  have h1 := mul_le_mul (hLw.trans ht) (hmax hn)
    (NNReal.coe_nonneg (max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3)))))
    (Real.exp_pos P).le
  have h2 := mul_le_mul hn (hmax (hcw.trans ht))
    (NNReal.coe_nonneg (max 1 (Real.toNNReal cw))) (Real.exp_pos P).le
  have he : Real.exp P * Real.exp P = Real.exp (2 * P) := by
    rw [← Real.exp_add]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1; norm_num
  calc
    _ ≤ 2 * Real.exp (2 * P) := by
      change (Lw : ℝ) * ((max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) : ℝ≥0) : ℝ) +
        Real.exp (3 * Pnative + 3) * ((max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤ _
      rw [he] at h1 h2
      linarith
    _ ≤ Real.exp 1 * Real.exp (2 * P) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [P]; ring

theorem native_product_bounds
    {pw cw Ptest : ℝ} {Lw : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (hPtest : 0 ≤ Ptest) (hLw : (Lw : ℝ) ≤ Real.exp Ptest)
    (hpw : pw ≤ Real.exp Ptest) (hcw : cw ≤ Real.exp Ptest) :
    let P := max Ptest (3 * Pnative + 3)
    ∀ i : data.Term,
      ((Lw * max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) +
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩ * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
          Real.exp (2 * P + 1) ∧
      ((W.cover * (data.twists i).cover : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) ∧
      ((W.modulus * (data.twists i).modulus : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) := by
  intro P i
  have ht : Real.exp Ptest ≤ Real.exp P := Real.exp_le_exp.mpr (le_max_left _ _)
  have hn : Real.exp (3 * Pnative + 3) ≤ Real.exp P := Real.exp_le_exp.mpr (le_max_right _ _)
  exact W.productUniform_exp_bounds (data.twists i) (hPtest.trans (le_max_left _ _))
    (hLw.trans ht) hn (hpw.trans ht) (hcw.trans ht) hn hn

end Erdos3.VectorPolynomial.ActualForecastData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ActualFixedSpatialPhysicalPolynomialRange
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem physicalPolynomial_uncenter
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    path.physicalPolynomial (fun j => subtractConstant (-(path.center j).val) (poly j)) = poly := by
  funext j
  change subtractConstant (path.center j).val
    (subtractConstant (-(path.center j).val) (poly j)) = poly j
  simpa only [neg_neg] using subtractConstant_neg_cancel (-(path.center j).val) (poly j)

omit [Fintype Tsp] in
theorem forall_physicalPolynomial_of_universal
    (Ptest : (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) →
      (∀ j d, coefficients (poly j) d ∈ U j) → Prop)
    (h : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hp : ∀ j d, coefficients (poly j) d ∈ U j),
      Ptest (path.physicalPolynomial poly) (path.physicalPolynomial_mem poly hp))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j d, coefficients (poly j) d ∈ U j) : Ptest poly hp := by
  let uncentered := fun j => subtractConstant (-(path.center j).val) (poly j)
  have hu : ∀ j d, coefficients (uncentered j) d ∈ U j :=
    fun j => coefficients_subtractConstant_mem (U j) (-path.center j) (poly j) (hp j)
  have hh := h uncentered hu
  have he : path.physicalPolynomial uncentered = poly := path.physicalPolynomial_uncenter poly
  simpa only [he] using hh

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

theorem targetAt_eq_rawTarget
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j) (κ : ℝ) (u : X → ℤ) :
    slice.targetAt selected hB o bW hb poly hm κ u =
      slice.rawTarget selected hB o bW hb κ (slice.path.physicalPolynomial poly)
        (slice.path.physicalPolynomial_mem poly hm) u := by
  rfl

theorem rawTarget_universal_approx
    {Findex : Type} [Fintype Findex] {period cover : ℝ} {L : ℝ≥0}
    (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) period cover L)
    (c : Findex → ℂ) (κ δ : ℝ)
    (h : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.targetAt selected hB o bW hb poly hm κ u -
        ∑ i, c i * (F i).eval physicalN (slice.path.physicalPolynomial poly) u‖ ≤ δ) :
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.rawTarget selected hB o bW hb κ poly hm u -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ := by
  apply slice.path.forall_physicalPolynomial_of_universal
    (fun poly hm => ∀ u, ‖slice.rawTarget selected hB o bW hb κ poly hm u -
      ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
  intro poly hm u
  simpa only [slice.targetAt_eq_rawTarget selected hB o bW hb poly hm κ u] using h poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

theorem rawTarget_actualForecastData_approx
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {Pnative massLog capLog E : ℝ}
    (data : ActualForecastData physicalN originalpoly Pnative massLog capLog E)
    (hc : data.centerConstant = fun j => (slice.path.center j).val)
    (κ : ℝ)
    (h : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.targetAt selected hB o bW hb poly hm κ u -
        ∑ i, data.coefficient i * (data.twists i).eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-E)) :
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.rawTarget selected hB o bW hb κ poly hm u -
        ∑ i, data.coefficient i * (data.twists i).eval physicalN poly u‖ ≤ Real.exp (-E) := by
  apply slice.rawTarget_universal_approx selected hB o bW hb data.twists data.coefficient
    κ (Real.exp (-E))
  intro poly hm u
  change ‖slice.targetAt selected hB o bW hb poly hm κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (slice.path.center j).val (poly j)) u‖ ≤ Real.exp (-E)
  simpa only [hc] using h poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedDataComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (slice.path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Eprec Rrank : ℝ} (hEprec : 0 ≤ Eprec)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail ν hlattice hcompact hmargin htrimbase
  hcenter hκ hUniversal hPtest hLw hpw hcw hEprec hlarge hRrank hrank hcutoff hδgrid
  hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt in

theorem native_ambient_comparison_actualForecastData :
    ‖slice.nativeMean s W originalpoly -
      (𝔼 u ∈ integerBox physicalN,
        W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
          slice.rawTarget (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ
            (slice.path.physicalPolynomial originalpoly)
            (slice.path.physicalPolynomial_mem originalpoly hmem) u)‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := Real.exp (-Edata)) (M := Real.exp massLog)
        (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  have hV : 0 < (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) := by
    apply Finset.prod_pos
    intro a _
    exact_mod_cast basisAxisScale_pos (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2
  have hPa : 0 ≤ (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) := (by linarith [s.hP] : (0 : ℝ) ≤ s.P).trans (le_max_left _ _)
  have hbds := data.native_product_bounds W hPtest hLw hpw hcw
  have hLip := data.native_product_lipschitz_bound W hPtest hLw hcw
  have hexp : Real.exp (2 * max Ptest (3 * Pnative + 3) + 1) ≤ Real.exp (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  have happ := slice.rawTarget_actualForecastData_approx (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb
    originalpoly data hcenter s.κ hUniversal
  have hcomp := slice.native_ambient_comparison_s2
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := ht) (hσbound := hσbound) (hδ := hδ) (hδone := hδone)
    (hdense := hdense) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := hsizeG) (hsmallG := hsmallG) (hsize := hsize) (hsmall := hsmall)
    (hε := hε) (hmesh := hmesh) (hη := hη) (htail := htail)
    (gridVolume := (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ))) (hVpos := hV) (ν := ν) (hmargin := hmargin)
    (htrimbase := htrimbase) (F := data.twists) (nativeCoeff := data.coefficient)
    (δnative := Real.exp (-Edata)) (happrox := by simpa only [rawTarget, hκ] using happ)
    (hPambient := hPa) (hEprec := hEprec) (hPP := le_max_left _ _)
    (hLip := hLip.trans hexp) (hcoverF := fun i => (hbds i).2.1.trans hexp)
    (hmodF := fun i => (hbds i).2.2.trans hexp) (hmass := data.mass)
    (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank) (cutoff := cutoff)
    (hcutoff := hcutoff) (hδgrid := hδgrid) (hδgrid1 := hδgrid1) (hgridmesh := hgridmesh)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
  simpa only [rawTarget, hκ] using hcomp

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail ν hlattice hcompact hmargin htrimbase
  hcenter hκ hUniversal hPtest hLw hpw hcw hEprec hlarge hRrank hrank hcutoff hδgrid
  hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt hfinite htarget in

theorem native_ambient_model_comparison_s2_oai :
    ‖slice.nativeMean s W originalpoly -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := Real.exp (-Edata)) (M := Real.exp massLog)
        (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  have hc := slice.native_ambient_comparison_actualForecastData
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := ht) (hσbound := hσbound) (hδ := hδ) (hδone := hδone)
    (hdense := hdense) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := hsizeG) (hsmallG := hsmallG) (hsize := hsize) (hsmall := hsmall)
    (hε := hε) (hmesh := hmesh) (hη := hη) (htail := htail)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (cutoff := cutoff) (hcutoff := hcutoff) (hδgrid := hδgrid) (hδgrid1 := hδgrid1)
    (hgridmesh := hgridmesh) (C := C) (hglobal := hglobal) (hz := hz)
    (hsampleAt := hsampleAt) (hreadAt := hreadAt)
  have he := FiniteProbabilityWeights.uniformFinset_complexMean (integerBox physicalN) hfinite
    (fun u => W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
      slice.rawTarget (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ
        (slice.path.physicalPolynomial originalpoly)
        (slice.path.physicalPolynomial_mem originalpoly hmem) u)
  rw [← he] at hc
  have hfunctions :
      (fun u : integerBox physicalN => W.eval physicalN
        (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u) =
      (fun u : integerBox physicalN => W.eval physicalN
        (slice.path.physicalPolynomial originalpoly) u.val *
        slice.rawTarget (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ
          (slice.path.physicalPolynomial originalpoly)
          (slice.path.physicalPolynomial_mem originalpoly hmem) u.val) := by
    funext u
    rw [hcenter, htarget]
    rfl
  rw [hfunctions]
  exact hc

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison_s2_oai
