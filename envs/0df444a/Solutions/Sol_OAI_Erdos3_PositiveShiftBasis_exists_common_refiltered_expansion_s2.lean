-- Prove2me | solution 1 for OAI.Erdos3.PositiveShiftBasis.exists_common_refiltered_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:20:03.715977+00:00
-- url     : https://prove2.me/submissions/4f908401-9147-4ba7-9a45-e1aef5cce692

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B193
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_controlled_refiltered_recovered_expansion_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (ν : κ → ι)
  (hν : ∀ x k, e.repr (φ x) k = b.repr x (ν k))

include hν in
theorem realificationLieHom_repr_of_coordinate (x : ℝ ⊗[ℚ] L) (k : κ) :
    (e.baseChange ℝ).repr (realificationLieHom φ x) k = (b.baseChange ℝ).repr x (ν k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, hν]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

namespace NilpotentLieFiltration

variable {σ : Type*} {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

include hν in
theorem realPolynomialGroupMap_slow (T : σ → ℝ) (R : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T R g) :
    G.PolynomialSlowBound e w T R (F.realPolynomialGroupMap G φ hφ w g) := by
  intro α k
  change |(e.baseChange ℝ).repr (coefficients
    ((F.realPolynomialGroupMap G φ hφ w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α) k| ≤ _
  rw [realPolynomialGroupMap_log, coefficients_map]
  change |(e.baseChange ℝ).repr (realificationLieHom φ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) k| ≤ _
  rw [realificationLieHom_repr_of_coordinate b e φ ν hν]
  exact hg α (ν k)

include hν in
theorem realPolynomialGroupMap_rational (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    G.PolynomialRationalGrid e w q (F.realPolynomialGroupMap G φ hφ w g) := by
  obtain ⟨z, hz⟩ := hg
  refine ⟨fun x => z (x.1, ν x.2), ?_⟩
  funext x
  change (z (x.1, ν x.2) : ℝ) = (q : ℝ) * (e.baseChange ℝ).repr
    (coefficients ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) x.1) x.2
  rw [realPolynomialGroupMap_log, coefficients_map]
  change (z (x.1, ν x.2) : ℝ) = (q : ℝ) * (e.baseChange ℝ).repr
    (realificationLieHom φ (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) x.1)) x.2
  rw [realificationLieHom_repr_of_coordinate b e φ ν hν]
  exact congrFun hz (x.1, ν x.2)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t e : ℕ} (F : NilpotentLieFiltration L s)
  (W : LieSubalgebra ℚ F.AssociatedGraded)
  (E : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s e)
  (hEF : E.filtration = F.gradedRefiltration W) (w : σ → ℕ)

theorem refiltered_polynomial_projection (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : (F.realification.adaptedPolynomialFiltration w).Group)
    (g : E.filtration.realification.PolynomialOrbit w)
    (hg : ∀ x : σ → ℤ,
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        (E.filtration.realification.polynomialOrbitEval w x g) =
          F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b)
    (x : σ → ℤ) :
    G.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (F.realPolynomialGroupMap G φ hφ w b) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) (φ.comp (F.gradedRefiltrationSubalgebra W).incl)
        (E.filtration.realification.polynomialOrbitEval w x g) := by
  rw [realPolynomialGroupMap_value, ← hg x]
  apply NilpotentLieBCHGroup.ext
  change φ.toLinearMap.baseChange ℝ
    ((F.gradedRefiltrationSubalgebra W).incl.toLinearMap.baseChange ℝ _) =
      (φ.toLinearMap.comp (F.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ _
  rw [LinearMap.baseChange_comp]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftProductData
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J)

variable {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

theorem anchoredFactors_geometry {p : ℝ} (hqp : q ≤ p)
    (hD : ∀ j, (D j).GeometryComplexityLE p) (hE : ∀ j, (E j).GeometryComplexityLE p) :
    ∀ i, (B.anchoredFactors D E i).GeometryComplexityLE p := by
  intro i
  rcases i with _ | ((_ | j) | j)
  · exact B.geometry.mono B.model hqp
  · exact B.geometry.mono B.model hqp
  · exact hD j
  · exact hE j

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

omit [DecidableEq ι] in
theorem realProductFinBasis_repr (x : ℝ ⊗[ℚ] (∀ i, L i))
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    ((pi D).basis.baseChange ℝ).repr x k =
      ((D z.1).basis.baseChange ℝ).repr (realificationLieHom (liePiEval z.1) x) z.2 := by
  dsimp only
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [Basis.baseChange_repr_tmul, realificationLieHom_tmul,
      productFinBasis_repr D, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem productExpansionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ productExpansionBudget p ∧ p ≤ productExpansionBudget p ∧
      (2 * p + 4) ^ 2 ≤ productExpansionBudget p := by
  dsimp [productExpansionBudget]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  · linarith

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

namespace RationalFilteredNilmanifold

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (f : κ → ι)

theorem productRestriction_coordinates (x : ∀ i, L i)
    (k : Fin (Fintype.card (Σ j : κ, Fin (d (f j))))) :
    (pi (fun j => D (f j))).basis.repr (liePiMap (fun j => liePiEval (R := ℚ) (f j)) x) k =
      (pi D).basis.repr x (productRestrictionIndex (d := d) f k) := by
  rw [productFinBasis_repr]
  exact productFinBasis_repr_component D x _ _

theorem productRestriction_layers (j : ℕ) (x : ∀ i, L i)
    (hx : x ∈ (pi D).filtration.layer j) :
    liePiMap (fun k => liePiEval (R := ℚ) (f k)) x ∈ (pi (fun k => D (f k))).filtration.layer j := by
  apply (mem_pi_layer (fun k => (D (f k)).filtration) j _).mpr
  intro k
  exact (mem_pi_layer (fun i => (D i).filtration) j x).mp hx (f k)

theorem productRestriction_lattice :
    (pi D).lattice ≤ (pi (fun j => D (f j))).lattice.comap
      (mapOfSteps (hL := (pi D).filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun j => D (f j))).filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun j => liePiEval (R := ℚ) (f j)))) := by
  intro x hx
  apply (mem_piBCHSubgroup _ _ _).mpr
  intro j
  exact (mem_piBCHSubgroup _ _ x).mp hx (f j)

theorem productRestriction_realLattice (x : (pi D).RealGroup) (hx : x ∈ (pi D).realLattice) :
    realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi (fun j => D (f j))).filtration.lowerCentralSeries_eq_bot)
      (liePiMap (fun j => liePiEval (R := ℚ) (f j))) x ∈ (pi (fun j => D (f j))).realLattice :=
  realificationMap_subgroup _ _ _ (productRestriction_lattice D f) hx

theorem productRestriction_piRealOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map ((realificationLieHom (liePiMap (fun j => liePiEval (R := ℚ) (f j)))).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (D i).filtration) g).log =
        (piRealOrbit (fun j => (D (f j)).filtration) (fun j => g (f j))).log := by
  apply coefficients.injective
  ext α
  apply ((pi (fun j => D (f j))).basis.baseChange ℝ).repr.injective
  ext k
  rw [realProductFinBasis_repr, realProductFinBasis_repr, coefficients_map]
  let z := (Fintype.equivFin (Σ j : κ, Fin (d (f j)))).symm k
  change ((D (f z.1)).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval z.1)
      (realificationLieHom (liePiMap (fun j => liePiEval (R := ℚ) (f j)))
        (coefficients (piRealOrbit (fun i => (D i).filtration) g).log α))) z.2 =
    ((D (f z.1)).basis.baseChange ℝ).repr (realificationLieHom (liePiEval z.1)
      (coefficients (piRealOrbit (fun j => (D (f j)).filtration) (fun j => g (f j))).log α)) z.2
  rw [realification_liePiEval_liePiMap]
  have hleft := congrArg (fun p => coefficients p α)
    (piRealOrbit_projection_log (fun i => (D i).filtration) g (f z.1))
  have hright := congrArg (fun p => coefficients p α)
    (piRealOrbit_projection_log (fun j => (D (f j)).filtration) (fun j => g (f j)) z.1)
  simp only [coefficients_map] at hleft hright
  exact congrArg (fun x => ((D (f z.1)).basis.baseChange ℝ).repr x z.2)
    (hleft.trans hright.symm)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansion
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem refiltered_product_expansion_of_recovered
    (hEF : E.filtration = (pi D).filtration.gradedRefiltration W)
    {p cost : ℝ} {q r : ℕ} (hbase : RefilteredRecoveredExpansionSpec D a W E Q p q r cost) :
    RefilteredProductExpansionSpec D a W E Q p q r cost := by
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, _, _, Λ,
    hΛ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout, hV, hbase⟩ := hbase
  refine ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant g horbit slow middle rat κ hκ hfactor hslow hrat hcoeff hzero hinput
  let F := (pi D).filtration
  let w := fun _ : Unit => 1
  have hπa (j : ℕ) (x : ∀ i, L i) (hx : x ∈ F.layer j) :
      liePiEval (R := ℚ) a x ∈ (D a).filtration.layer j :=
    (mem_pi_layer (fun i => (D i).filtration) j x).mp hx a
  let πz := liePiMap (fun i : I₀ => (liePiEval i.val : (∀ j, L j) →ₗ⁅ℚ⁆ L i.val))
  have hπz (j : ℕ) (x : ∀ i, L i) (hx : x ∈ F.layer j) : πz x ∈ Z.filtration.layer j := by
    rw [hZF]
    exact productRestriction_layers D (fun i : I₀ => i.val) j x hx
  let pa := F.realPolynomialGroupMap (D a).filtration (liePiEval (R := ℚ) a) hπa w
  let pz := F.realPolynomialGroupMap Z.filtration πz hπz w
  let κa := fun h => productProjectionHom D a (κ h)
  let κz := fun h => realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := Z₀.filtration.lowerCentralSeries_eq_bot) πz (κ h)
  choose b hb using fun h => F.exists_model_refiltered_polynomial W E hEF w
    (fun _ => Nat.zero_lt_one) (middle h) (hcoeff h) (hzero h)
  have hκa (h) : κa h ∈ (D a).realLattice :=
    realificationMap_subgroup _ _ _ (productProjection_lattice D a) (hκ h)
  have hκz (h) : κz h ∈ Z₀.realLattice :=
    productRestriction_realLattice D (fun i : I₀ => i.val) (κ h) (hκ h)
  have hpaOrbit (h) : pa ⟨⟨(piRealOrbit (fun i => (D i).filtration) (g h)).log,
        (piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩ =
      ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩ := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    change VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ) a)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (D i).filtration) (g h)).log = (S h).orbit.log
    rw [piRealOrbit_projection_log, horbit]
  have hfactorA (h) : pa (slow h) * pa (middle h) * pa (rat h) *
      (D a).filtration.realification.adaptedConstantGroupHom w (κa h) =
        ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩ := by
    have hh := congrArg pa (hfactor h)
    rw [map_mul, map_mul, map_mul, hpaOrbit] at hh
    exact hh
  let ia := fun k => Fintype.equivFin (Σ i, Fin (d i)) ⟨a, k⟩
  have hca (x : ∀ i, L i) (k) : (D a).basis.repr (liePiEval (R := ℚ) a x) k =
      (pi D).basis.repr x (ia k) := productFinBasis_repr_component D x a k
  have hcz (x : ∀ i, L i) (k) : Z.basis.repr (πz x) k =
      (pi D).basis.repr x (productRestrictionIndex (d := d) (fun i : I₀ => i.val) k) := by
    rw [hZb]
    exact productRestriction_coordinates D (fun i : I₀ => i.val) x k
  have hslowA (h) : (D a).filtration.PolynomialSlowBound (D a).basis w
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (pa (slow h)) :=
    realPolynomialGroupMap_slow (pi D).basis (D a).basis (liePiEval (R := ℚ) a) ia hca
      F (D a).filtration hπa w _ _ (slow h) (hslow h)
  have hratA (h) : (D a).filtration.PolynomialRationalGrid (D a).basis w q (pa (rat h)) :=
    realPolynomialGroupMap_rational (pi D).basis (D a).basis (liePiEval (R := ℚ) a) ia hca
      F (D a).filtration hπa w q (rat h) (hrat h)
  have hslowZ (h) : Z.filtration.PolynomialSlowBound Z.basis w
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (pz (slow h)) :=
    realPolynomialGroupMap_slow (pi D).basis Z.basis πz
      (productRestrictionIndex (d := d) (fun i : I₀ => i.val)) hcz F Z.filtration hπz w _ _
      (slow h) (hslow h)
  have hratZ (h) : Z.filtration.PolynomialRationalGrid Z.basis w q (pz (rat h)) :=
    realPolynomialGroupMap_rational (pi D).basis Z.basis πz
      (productRestrictionIndex (d := d) (fun i : I₀ => i.val)) hcz F Z.filtration hπz w q
      (rat h) (hrat h)
  have hmiddleA (h x) : (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
      (pa (middle h)) = realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
        (E.filtration.realification.polynomialOrbitEval w x (b h)) :=
    F.refiltered_polynomial_projection W E w (D a).filtration (liePiEval (R := ℚ) a) hπa
      (middle h) (b h) (hb h) x
  have hmapz : πz.comp H.incl = liePiMap (fun i : I₀ => refilteredComponentMap D W i.val) := by
    ext x i
    rfl
  have hmiddleZ (h x) : Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
      (pz (middle h)) = realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
        (E.filtration.realification.polynomialOrbitEval w x (b h)) := by
    have hh := F.refiltered_polynomial_projection W E w Z.filtration πz hπz
      (middle h) (b h) (hb h) x
    rw [hmapz] at hh
    exact hh
  let gz := fun h => piRealOrbit (fun i : I₀ => (D i.val).filtration) (fun i : I₀ => g h i.val)
  let fz := fun h x => Z₀.filtration.realification.polynomialOrbitEval w x (gz h)
  have hfactorZ (h x) : Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (pz (slow h)) *
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
        (E.filtration.realification.polynomialOrbitEval w x (b h)) *
      Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (pz (rat h)) * κz h = fz h x := by
    rw [← hmiddleZ h x]
    have hh := congrArg (fun v => Z.filtration.adaptedPolynomialRealValueHom w
      (fun i => (x i : ℝ)) (pz v)) (hfactor h)
    simp only [map_mul] at hh
    have hc : pz (F.realification.adaptedConstantGroupHom w (κ h)) =
        Z.filtration.realification.adaptedConstantGroupHom w (κz h) :=
      F.realPolynomialGroupMap_constant Z.filtration πz hπz w (κ h)
    rw [hc, adaptedPolynomialRealValueHom_constant] at hh
    refine hh.trans ?_
    apply NilpotentLieBCHGroup.ext
    change eval₂ (fun i => (x i : ℝ))
      (VectorPolynomial.map ((realificationLieHom πz).toLinearMap.restrictScalars ℚ)
        (piRealOrbit (fun i => (D i).filtration) (g h)).log) = _
    rw [productRestriction_piRealOrbit_log]
    exact congrArg NilpotentLieBCHGroup.coord
      (Z₀.filtration.realification.polynomialOrbitRealEval_integer w (gz h) x)
  exact hbase freq hfreq N A B label hρ hK hA hB hAsum hBsum hres hcircle S hS hpositive hinvariant
    (fun h => pa (slow h)) (fun h => pa (middle h)) (fun h => pa (rat h)) κa b
    hκa hfactorA hslowA hratA hmiddleA (fun h => pz (slow h)) (fun h => pz (rat h))
    κz fz hκz hfactorZ hslowZ hratZ hinput

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_controlled_refiltered_product_expansion (s r : ℕ) :
    ∃ A B : ℕ, 2 ≤ A ∧ 2 ≤ B ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + A) ^ A) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + A) ^ A) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + A) ^ A) ∧
            RefilteredProductExpansionSpec D a W E Q p q r (((p + A) ^ A + B) ^ B) := by
  obtain ⟨A, B, hA, hB, hmodels⟩ := exists_controlled_refiltered_recovered_expansion_s2 s r
  refine ⟨A, B, hA, hB, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hbase⟩ :=
    hmodels D a w hF W v₀ hspan hp hι hD hκ hv q hq hqp
  exact ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget,
    refiltered_product_expansion_of_recovered D a W E Q hEF hbase⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem exists_common_refiltered_expansion_s2_oai (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonRefilteredExpansionSpec s r C := by
  classical
  obtain ⟨c, k, _, _, hmodels⟩ := exists_controlled_refiltered_product_expansion s r
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  dsimp only [CommonRefilteredExpansionSpec]
  intro N _ q a J B L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E A R anchor H p F hp hqp hD hE
  let T := B.anchoredFactors D E
  let t := productExpansionBudget p
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨ht, hpt, hsq⟩ := productExpansionBudget_bounds hp0
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hpi : p ≤ 2 * p + 2 := by linarith
  have hm : (B.count : ℝ) ≤ p :=
    (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hcard : (Fintype.card (Option (Option (Fin B.count) ⊕ Fin B.count)) : ℝ) ≤ 2 * p + 2 := by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    linarith
  have hgeometry (i) : (T i).GeometryComplexityLE p := B.anchoredFactors_geometry D E hqp hD hE i
  have hprod : (pi T).GeometryComplexityLE ((2 * p + 4) ^ 2) := by
    convert pi_geometry T (by linarith : 0 ≤ 2 * p + 2) hcard
      (fun i => (hgeometry i).mono (T i) hpi) using 1
    ring
  have hcardt : (Fintype.card (Option (Option (Fin B.count) ⊕ Fin B.count)) : ℝ) ≤ t := by
    dsimp [t, productExpansionBudget]
    nlinarith [sq_nonneg (2 * p + 3)]
  have hspanning :
      (Fintype.card (Σ i, Fin (B.anchoredDimension d e i)) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hprod.1.trans hsq
  have hbud : (t + c) ^ c + ((t + c) ^ c + k) ^ k ≤ (t + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget t ht0
  have hgeom : (t + c) ^ c ≤ (t + C) ^ C := by
    have : 0 ≤ ((t + c) ^ c + k) ^ k := by positivity
    linarith
  have hcost : ((t + c) ^ c + k) ^ k ≤ (t + C) ^ C := by
    have : 0 ≤ (t + c) ^ c := by positivity
    linarith
  obtain ⟨U, hUF, hUL, hU, n, hn, Q, hQF, hQL, hQ, htarget, hexp⟩ :=
    hmodels T none F.weight F.adapted F.subalgebra F.spanning F.span_eq
      (by dsimp [t]; linarith) hcardt (fun i => (hgeometry i).mono (T i) hpt) (by simpa only [Fintype.card_fin] using hspanning)
      (fun i j => (F.height i j).trans hpt) F.denominator F.denominator_pos
      (F.denominator_bound.trans (Real.exp_le_exp.mpr hpt))
  exact ⟨U, hUF, hUL, hU.mono U hgeom, n, hn, Q, hQF, hQL, hQ.mono Q hgeom,
    htarget.mono (nativeRefilteredTarget T none F.subalgebra U Q) hgeom,
    ((t + c) ^ c + k) ^ k, by positivity, hcost, hexp⟩

end Erdos3.PositiveShiftBasis

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.PositiveShiftBasis.exists_common_refiltered_expansion_s2_oai := @OAI.Erdos3.PositiveShiftBasis.exists_common_refiltered_expansion_s2_oai
