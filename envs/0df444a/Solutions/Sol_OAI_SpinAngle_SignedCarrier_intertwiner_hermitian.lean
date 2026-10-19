-- Prove2me | solution 1 for OAI.SpinAngle.SignedCarrier.intertwiner_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:23:06.133782+00:00
-- url     : https://prove2.me/submissions/74947756-3e5d-4363-b2c2-3b30d28e493d

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/SpinAngle/Core.lean:L1884-L1902
-- (upload_full_project.md Phase 4): solution for node OAI.SpinAngle.SignedCarrier.intertwiner_hermitian. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

-- ---- from OAI.RepresentationTheory.SpinAngle.Core ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
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

include hc in
lemma repr_diagonal (a : n → ℂ) (f : F) (y : Y) :
    c.repr (D' a f) y = (∏ j, a j ^ v y j) * c.repr f y := by
  classical
  calc
    c.repr (D' a f) y = c.repr (D' a (∑ k, c.repr f k • c k)) y := by rw [c.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, hc,
        Basis.repr_self]
      simp [Finset.sum_apply, Finsupp.single_apply, mul_comm]

lemma coefficient_zero
    {n : Type*} {X : Type*} {Y : Type*} {E : Type*} {F : Type*}
    [contextInstance1400_29 : Fintype n]
    [Fintype X]
    [contextInstance1400_53 : Fintype Y]
    [contextInstance1401_2 : AddCommGroup E]
    [contextInstance1401_19 : Module ℂ E]
    [contextInstance1401_32 : AddCommGroup F]
    [contextInstance1401_49 : Module ℂ F]
    (b : Basis X ℂ E) (c : Basis Y ℂ F)
    (w : X → n → ℕ) (v : Y → n → ℕ)
    (D : (n → ℂ) → E →ₗ[ℂ] E) (D' : (n → ℂ) → F →ₗ[ℂ] F)
    (hb : ∀ a x, D a (b x) = (∏ j, a j ^ w x j) • b x)
    (hc : ∀ a y, D' a (c y) = (∏ j, a j ^ v y j) • c y) (L : E →ₗ[ℂ] F)
    (hL : ∀ a : n → ℂ, (∀ j, star (a j) * a j = 1) → ∀ x, L (D a x) = D' a (L x))
    (x : X) (y : Y) (j : n) (hxy : w x j ≠ v y j) :
    c.repr (L (b x)) y = 0 := by
  classical
  let N := w x j + v y j + 1
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hN : N ≠ 0 := by dsimp [N]; omega
  have hz : IsPrimitiveRoot z N := Complex.isPrimitiveRoot_exp _ hN
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz.pow_eq_one hN
  have hzu : star z * z = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]
    norm_num
  let a : n → ℂ := fun k => if k = j then z else 1
  have ha : ∀ k, star (a k) * a k = 1 := by
    intro k
    dsimp [a]
    split_ifs
    · exact hzu
    · simp
  have hh := congrArg (fun f => c.repr f y) (hL a ha (b x))
  rw [hb, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
    repr_diagonal c v D' hc] at hh
  have hprod (u : n → ℕ) : (∏ k, a k ^ u k) = z ^ u j := by
    simp [a]
  rw [hprod, hprod] at hh
  by_contra hn
  exact hxy (hz.pow_inj (by dsimp [N]; omega) (by dsimp [N]; omega)
    (mul_right_cancel₀ hn hh))

include b c w v hb hc in

theorem diagonal (L : E →ₗ[ℂ] F)
    (hL : ∀ a : n → ℂ, (∀ j, star (a j) * a j = 1) → ∀ x, L (D a x) = D' a (L x))
    (a : n → ℂ) : L.comp (D a) = (D' a).comp L := by
  classical
  apply b.ext
  intro x
  apply c.repr.injective
  ext y
  simp only [LinearMap.comp_apply, hb, map_smul, Finsupp.smul_apply, smul_eq_mul,
    repr_diagonal c v D' hc]
  by_cases hw : w x = v y
  · rw [hw]
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp hw
    rw [coefficient_zero b c w v D D' hb hc L hL x y j hj]
    simp

end SpinAngle.TorusNaturality

namespace SpinAngle.SignedTensor
open scoped Classical Matrix TensorProduct InnerProductSpace
open Module
variable {q : ℕ}
variable {ι κ τ : Type*} [contextInstance1517_25 : Fintype ι] [contextInstance1517_37 : DecidableEq ι] [contextInstance1517_53 : Fintype κ] [contextInstance1517_65 : DecidableEq κ]
  [contextInstance1518_2 : Fintype τ] [contextInstance1518_14 : DecidableEq τ]

lemma pairRep_unitary (g : Group q) (v w : PairRaw (q := q) (ι := ι) (κ := κ)) :
    ⟪pairRep g v,pairRep g w⟫_ℂ = ⟪v,w⟫_ℂ :=
  ExternalTensor.unitary (TensorRep.rep (ι := ι) (n := Fin q)) (TensorRep.rep (ι := κ) (n := Fin q))
    TensorRep.rep_unitary TensorRep.rep_unitary g v w

lemma block_diagPair (a : Spin q → ℂ) : block (diagPair a) = Matrix.diagonal a := by
  change Matrix.blockDiagonal (fun b : Bool => cond b (Matrix.diagonal (fun j => a (j,true))) (Matrix.diagonal (fun j => a (j,false)))) = Matrix.diagonal a
  convert Matrix.blockDiagonal_diagonal (fun (b : Bool) (j : Fin q) => a (j,b)) using 1
  congr 1
  funext b
  cases b <;> rfl

lemma pairBasis_diagonal (a : Spin q → ℂ) (x : (ι → Fin q) × (κ → Fin q)) :
    pairAction (diagPair a) (pairBasis x) =
      (∏ j, a j ^ pairContent x j) • pairBasis x := by
  simp only [pairBasis, OrthonormalBasis.tensorProduct_apply', EuclideanSpace.basisFun_apply,
    pairAction_tmul, diagPair, TensorRep.diagonal_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_smul]
  congr 1
  rw [Fintype.prod_prod_type]
  simp only [pairContent, Fintype.prod_bool, Bool.cond_false, Bool.cond_true]
  rw [Finset.prod_mul_distrib, TensorRep.product_content (fun j : Fin q => a (j,true)) x.2,
    TensorRep.product_content (fun j : Fin q => a (j,false)) x.1]

theorem intertwiner_diagonal
    (L : PairRaw (q := q) (ι := ι) (κ := κ) →ₗ[ℂ] Raw (q := q) (τ := τ))
    (hL : ∀ g : Group q, ∀ v, L (pairRep g v) = rep g (L v))
    (a : Spin q → ℂ) (v : PairRaw (q := q) (ι := ι) (κ := κ)) :
    L (pairAction (diagPair a) v) = TensorRep.action (Matrix.diagonal a) (L v) := by
  have hh := TorusNaturality.diagonal (pairBasis (q := q) (ι := ι) (κ := κ)).toBasis
    (EuclideanSpace.basisFun (τ → Spin q) ℂ).toBasis pairContent TensorRep.content
    (fun a => pairAction (diagPair a)) (fun a => TensorRep.action (Matrix.diagonal a))
    pairBasis_diagonal (fun a x => by
      simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, TensorRep.product_content] using
        (TensorRep.diagonal_single a x)) L (fun a ha v => by
      let g : Group q :=
        (⟨(diagPair a).1, TensorRep.diagonal_unitary_of_star_mul _ (fun j => ha (j,false))⟩,
         ⟨(diagPair a).2, TensorRep.diagonal_unitary_of_star_mul _ (fun j => ha (j,true))⟩)
      have hh := hL g v
      change L (pairAction (diagPair a) v) = TensorRep.action (block (diagPair a)) (L v) at hh
      rwa [block_diagPair] at hh) a
  exact congrArg (fun f : _ →ₗ[ℂ] _ => f v) hh

lemma pair_spectral (a : Mat q × Mat q) (ha : a.1.IsHermitian) (hb : a.2.IsHermitian) :
    ∃ (g : Group q) (d : Spin q → ℂ),
      a = (g.1.val,g.2.val) * diagPair d * (g.1⁻¹.val,g.2⁻¹.val) := by
  refine ⟨(ha.eigenvectorUnitary,hb.eigenvectorUnitary),
    (fun j => cond j.2 (hb.eigenvalues j.1 : ℂ) (ha.eigenvalues j.1 : ℂ)), ?_⟩
  apply Prod.ext
  · exact ha.spectral_theorem
  · exact hb.spectral_theorem

theorem intertwiner_hermitian
    (L : PairRaw (q := q) (ι := ι) (κ := κ) →ₗ[ℂ] Raw (q := q) (τ := τ))
    (hL : ∀ g : Group q, ∀ v, L (pairRep g v) = rep g (L v))
    (a : Mat q × Mat q) (ha : a.1.IsHermitian) (hb : a.2.IsHermitian)
    (v : PairRaw (q := q) (ι := ι) (κ := κ)) :
    L (pairAction a v) = TensorRep.action (block a) (L v) := by
  obtain ⟨g,d,he⟩ := pair_spectral a ha hb
  rw [he]
  simp only [map_mul, Module.End.mul_apply, block_diagPair]
  change L (pairRep g (pairAction (diagPair d) (pairRep g⁻¹ v))) =
    rep g (TensorRep.action (Matrix.diagonal d) (rep g⁻¹ (L v)))
  rw [hL, intertwiner_diagonal L hL, hL]

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

lemma inner_move
    {G : Type*}
    [contextInstance1640_21 : Group G]
    {E : Type*}
    [contextInstance1641_23 : NormedAddCommGroup E]
    [contextInstance1641_46 : InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E)
    (hρ : ∀ g x y, ⟪ρ g x,ρ g y⟫_ℂ = ⟪x,y⟫_ℂ) (g : G) (x y : E) : ⟪x,ρ g y⟫_ℂ = ⟪ρ g⁻¹ x,y⟫_ℂ := by
  have h := hρ g (ρ g⁻¹ x) y
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

include hρ hσ in
lemma adjoint_intertwines (L : E →ₗ[ℂ] F)
    (hL : ∀ g x, L (ρ g x) = σ g (L x)) (g : G) (y : F) :
    LinearMap.adjoint L (σ g y) = ρ g (LinearMap.adjoint L y) := by
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right, inner_move σ hσ, ← hL,
    ← LinearMap.adjoint_inner_right, ← inner_move ρ hρ]

lemma adjoint_isometry (L : E →ₗᵢ[ℂ] F) (x : E) :
    LinearMap.adjoint L.toLinearMap (L x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact L.inner_map_map y x

end SpinAngle.UnitaryNaturality

namespace SpinAngle.SignedCarrier
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor
variable (a b : YoungDiagram) (q : ℕ) (ha : a.colLen 0 ≤ q) (hb : b.colLen 0 ≤ q)

lemma inclusion_equivariant (g : Group q) (v : Carrier a b q ha hb) :
    inclusion a b q ha hb (rep a b q ha hb g v) =
      pairRep g (inclusion a b q ha hb v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp [hx,hy]

lemma rep_unitary (g : Group q) (v w : Carrier a b q ha hb) :
    ⟪rep a b q ha hb g v,rep a b q ha hb g w⟫_ℂ = ⟪v,w⟫_ℂ := by
  rw [← (inclusion a b q ha hb).inner_map_map,
    ← (inclusion a b q ha hb).inner_map_map v w,
    inclusion_equivariant, inclusion_equivariant]
  exact SignedTensor.pairRep_unitary g _ _

lemma inclusion_hermitianAction (A : Mat q × Mat q) (hA : A.1.IsHermitian) (hB : A.2.IsHermitian)
    (v : Carrier a b q ha hb) :
    inclusion a b q ha hb (hermitianAction a b q ha hb A hA hB v) =
      pairAction A (inclusion a b q ha hb v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [inclusion, hermitianAction, TensorProduct.mapIsometry_apply,
      TensorProduct.map_tmul, pairAction_tmul]
    change PolynomialCarrier.inclusion a q ha (PolynomialCarrier.hermitianAction a q ha A.1 hA x) ⊗ₜ[ℂ]
      PolynomialCarrier.inclusion b q hb (PolynomialCarrier.hermitianAction b q hb A.2 hB y) = _
    rw [PolynomialCarrier.inclusion_hermitianAction, PolynomialCarrier.inclusion_hermitianAction]
    rfl
  | add x y hx hy => simp [hx,hy]

variable {τ : Type*} [contextInstance1741_21 : Fintype τ] [contextInstance1741_33 : DecidableEq τ]

theorem intertwiner_hermitian
    (L : (rep a b q ha hb).IntertwiningMap (SignedTensor.rep (q := q) (τ := τ)))
    (A : Mat q × Mat q) (hA : A.1.IsHermitian) (hB : A.2.IsHermitian)
    (v : Carrier a b q ha hb) :
    L (hermitianAction a b q ha hb A hA hB v) = TensorRep.action (block A) (L v) := by
  let J := inclusion a b q ha hb
  let L' := L.toLinearMap.comp (LinearMap.adjoint J.toLinearMap)
  have hequiv (g : Group q) (x : PairRaw (q := q) (ι := Cells a) (κ := Cells b)) :
      L' (pairRep g x) = SignedTensor.rep g (L' x) := by
    dsimp [L']
    rw [UnitaryNaturality.adjoint_intertwines (rep a b q ha hb) pairRep
      (rep_unitary a b q ha hb) SignedTensor.pairRep_unitary J.toLinearMap
      (inclusion_equivariant a b q ha hb), L.isIntertwining]
  have h := SignedTensor.intertwiner_hermitian L' hequiv A hA hB (J v)
  have hj (x : Carrier a b q ha hb) : L' (J x) = L x := by
    dsimp [L']
    rw [UnitaryNaturality.adjoint_isometry]
  rw [← inclusion_hermitianAction a b q ha hb A hA hB v, hj, hj] at h
  exact h

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
end SpinAngle.MatrixAnalysis

namespace SpinAngle.TensorMatrix
open SpinAngle.MatrixAnalysis
variable {ι n : Type*} [contextInstance3707_23 : Fintype ι] [contextInstance3707_35 : DecidableEq ι] [contextInstance3707_51 : Fintype n] [contextInstance3707_63 : DecidableEq n]

end SpinAngle.TensorMatrix

noncomputable section
open scoped BigOperators
namespace SpinAngle

end SpinAngle

namespace SpinAngle
open scoped BigOperators
variable {ι : Type*} [contextInstance3841_21 : Fintype ι] [contextInstance3841_33 : DecidableEq ι]

variable {R C : Type*} [contextInstance3877_23 : Fintype R] [contextInstance3877_35 : DecidableEq R] [contextInstance3877_51 : Fintype C] [contextInstance3877_63 : DecidableEq C]

end SpinAngle

namespace SpinAngle.MatrixAnalysis
variable {n C : Type*} [contextInstance3931_23 : Fintype n] [contextInstance3931_35 : DecidableEq n] [contextInstance3931_51 : Fintype C] [contextInstance3931_63 : DecidableEq C]

end SpinAngle.MatrixAnalysis

namespace SpinAngle
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]

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
open OAI OAI.SpinAngle OAI.SpinAngle.SignedCarrier
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped Classical TensorProduct InnerProductSpace
open SpinAngle.Young SpinAngle.Specht PolynomialCarrier Module SignedTensor


theorem solution : type_of% @_root_.OAI.SpinAngle.SignedCarrier.intertwiner_hermitian := @_root_.OAI.SpinAngle.SignedCarrier.intertwiner_hermitian
