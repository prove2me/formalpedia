-- Prove2me | solution 1 for OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:18:26.8658+00:00
-- url     : https://prove2.me/submissions/5aec1016-973c-46cf-9543-484c87ac9d92

import Mathlib
import Definitions.Def_OAIQ124K023

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.piPiece_finite _root_.OAI.KLInvariance.Graded.subPiece_finite _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/

section

namespace KLInvariance.Hilbert

/-- Sum over all monomials in finitely many variables, before grouping by degree. -/
theorem hasSum_monomials (σ : Type*) [Fintype σ] {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ) := by
  classical
  apply Fintype.induction_empty_option (P := fun σ _ =>
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ))
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Fintype.card_congr e]
    apply (Equiv.piCongrLeft (fun _ : β => ℕ) e).hasSum_iff.mp
    convert ih using 1
    all_goals try with_reducible_and_instances rfl
    ext d
    simp only [Function.comp_apply, Equiv.piCongrLeft_apply]
    congr 1
    simpa using e.symm.sum_comp d
  · simp
  · intro α _ ih
    have hg := hasSum_geometric_of_lt_one hq hq1
    have hs := hg.summable.mul_of_nonneg ih.summable
      (fun _ => pow_nonneg hq _) (fun _ => pow_nonneg hq _)
    have hh := hg.mul ih hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hh
    simpa [Function.comp_def, Fintype.sum_option, pow_add, pow_succ, mul_comm] using he


lemma intWeight_eq_natWeight {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) d : ℕ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]

lemma polynomialGrading_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Graded.polynomialGrading k σ n =
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℕ)) n := by
  ext p
  change (∀ d, p.coeff d ≠ 0 →
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d = (n : ℤ)) ↔ _
  simp only [intWeight_eq_natWeight, Nat.cast_inj]
  rfl

instance polynomialPiece_finite (k : Type*) [Field k] (σ : Type*) [Finite σ] (n : ℤ) :
    Module.Finite k (Graded.polynomialGrading k σ n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [polynomialGrading_nat]
    exact Module.Finite.iff_fg.mpr
      (MvPolynomial.weightedHomogeneousSubmodule_fg k (fun _ : σ => 1) (by simp) m)
  · rw [Graded.polynomialGrading_negative k σ n (lt_of_not_ge hn)]
    infer_instance

lemma polynomial_finrank_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Module.finrank k (Graded.polynomialGrading k σ n) =
      Nat.card {d : σ →₀ ℕ // Finsupp.weight (fun _ => (1 : ℕ)) d = n} := by
  rw [polynomialGrading_nat, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k _)

lemma hasSum_finsupp_monomials (σ : Type*) [Fintype σ] {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ →₀ ℕ => q ^ Finsupp.weight (fun _ => (1 : ℕ)) d)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).hasSum_iff.mpr
    (hasSum_monomials σ hq hq1)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext d
  congr 1
  simp only [Finsupp.weight_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype d _ (by simp)

/-- The actual finite polynomial ring has Hilbert series `(1-q)⁻ᴺ`. -/
theorem hasSum_polynomial_nat (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (hasSum_finsupp_monomials σ hq hq1).tsum_fiberwise
    (Finsupp.weight (fun _ : σ => (1 : ℕ)))
  apply h.congr_fun
  intro n
  rw [polynomial_finrank_nat]
  have hf : (fun d : ↑((Finsupp.weight (R := ℕ) (fun _ : σ => (1 : ℕ))) ⁻¹' {n}) =>
      q ^ (Finsupp.weight (fun _ : σ => (1 : ℕ))) d.val) = fun _ => q^n := by
    funext d
    rw [show Finsupp.weight (fun _ : σ => (1 : ℕ)) d.val = n from d.property]
  rw [hf, tsum_const, nsmul_eq_mul]
  simp only [Set.preimage, Set.mem_singleton_iff]
  rfl


/-- Integer-indexed grading, including its zero negative pieces. -/
theorem hasSum_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  apply ((Nat.cast_injective : Function.Injective ((↑) : ℕ → ℤ)).hasSum_iff ?_).mp
  · simpa only [Function.comp_def, zpow_natCast] using hasSum_polynomial_nat k σ hq hq1
  · intro n hn
    have hn' : n < 0 := by
      by_contra h
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
      exact hn ⟨m, rfl⟩
    rw [Graded.polynomialGrading_negative k σ n hn']
    simp

end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

lemma shiftedPiece_finrank {ι : Type ui} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.finrank k (Graded.shiftedPiece 𝓐 d n) = ∑ i, Module.finrank k (𝓐 (n-d i)) := by
  rw [(shiftedPieceEquiv 𝓐 d n).finrank_eq, Module.finrank_pi_fintype]

lemma hasSum_shifted_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    (d : ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ (n-d)) : ℝ) * q^n)
      (q^d * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  have h := (hasSum_polynomial k σ hq.le hq1).mul_left (q^d)
  apply h.congr_fun
  intro n
  change (Module.finrank k (Graded.polynomialGrading k σ (n+d-d)) : ℝ) * q^(n+d) = _
  rw [add_sub_cancel_right, zpow_add₀ hq.ne']
  ring

/-- Convergent Hilbert series and its normalization for the actual shifted free module. -/
theorem hasSum_shiftedFree (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {ι : Type*} [Fintype ι] (d : ι → ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ =>
      (Module.finrank k (Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) : ℝ) * q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  have h := hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_shifted_polynomial k σ (d i) hq hq1)
  rw [← Finset.sum_mul] at h
  apply h.congr_fun
  intro n
  rw [shiftedPiece_finrank, Nat.cast_sum, Finset.sum_mul]


section FiniteModule
variable {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

lemma degreeMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) : Function.Surjective (degreeMap 𝓜 𝓝 f hf n) := by
  intro m
  obtain ⟨v,hv⟩ := hs m.val
  refine ⟨DirectSum.decompose 𝓜 v n, ?_⟩
  apply Subtype.ext
  change f (Graded.component 𝓜 n v) = m.val
  have h := Graded.map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero, hv] at h
  exact h.symm.trans (DirectSum.decompose_of_mem_same 𝓝 m.property)
end FiniteModule

section HomogeneousBasis
variable {σ : Type ua} [Fintype σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (Graded.polynomialGrading k σ) 𝓜]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι (MvPolynomial σ k) M)
  (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))

include hd

omit [Fintype σ] [IsScalarTower k (MvPolynomial σ k) M] [DirectSum.Decomposition 𝓜] in
lemma basis_equivFun_symm_graded (n : ℤ) (v : ι → MvPolynomial σ k)
    (hv : v ∈ Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) :
    b.equivFun.symm v ∈ 𝓜 n := by
  rw [b.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro i _
  simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)

lemma finrank_homogeneous_basis (n : ℤ) :
    Module.finrank k (𝓜 n) =
      ∑ i, Module.finrank k (Graded.polynomialGrading k σ (n-d i)) := by
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  let f := degreeMap (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜
    b.equivFun.symm.toLinearMap (basis_equivFun_symm_graded 𝓜 b d hd) n
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply b.equivFun.symm.injective
      exact congrArg Subtype.val h
    · exact degreeMap_surjective _ _ b.equivFun.symm.toLinearMap
        (basis_equivFun_symm_graded 𝓜 b d hd) b.equivFun.symm.surjective n
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  exact shiftedPiece_finrank _ d n

/-- The precise Hilbert normalization for a finite homogeneous basis, with the source's
convention that a generator in degree `d` contributes `q^d`. -/
theorem hasSum_homogeneous_basis {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (hasSum_shiftedFree k σ d hq hq1).congr_fun
  intro n
  rw [finrank_homogeneous_basis 𝓜 b d hd, shiftedPiece_finrank]
end HomogeneousBasis


end KLInvariance.Hilbert


end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]

attribute [instance] NonnegativeBasis.finite

namespace NonnegativeBasis
variable {𝓜} (b : NonnegativeBasis (σ := σ) 𝓜)

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma eval₂_eq (q : ℝ) : Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial =
    ∑ i, q ^ b.degree i := by
  change (Polynomial.eval₂RingHom (Int.castRingHom ℝ) q) (∑ i, X ^ b.degree i) = _
  simp

omit [Finite σ] in
lemma hasSum [Fintype σ] {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial * (1-q)⁻¹ ^ Fintype.card σ) := by
  rw [b.eval₂_eq]
  convert Hilbert.hasSum_homogeneous_basis 𝓜 b.basis (fun i => (b.degree i : ℤ))
    b.homogeneous hq hq1 using 1
  all_goals try with_reducible_and_instances rfl
  simp

end NonnegativeBasis

end KLInvariance.Graded

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Actual integral projection and support lattices inherit their grading from
the genuine tensor word. In particular a homogeneous stalk vector has a
homogeneous tensor lift. No freeness/character claim is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro h e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact h
  · intro h
    exact h ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

end
end KLInvariance.TitsSpace

end


section

/-! A homogeneous integral equivalence induces genuine shifted degreewise
vector-space equivalences, including its inverse grading. -/
namespace KLInvariance.Graded
universe uk um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]
  (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
  (e : M ≃ₗ[k] N) (d : ℤ)
  (he : ∀ n m, m ∈ 𝓜 n → e m ∈ 𝓝 (n+d))
noncomputable section

include e he in
 theorem finrank_homogeneousEquiv (n : ℤ) :
    Module.finrank k (𝓝 n)=Module.finrank k (𝓜 (n-d)) := by
  have h := (homogeneousPieceEquiv 𝓜 𝓝 e d he (n-d)).finrank_eq
  have hn : n-d+d=n := by omega
  rw [hn] at h
  exact h.symm

end
end KLInvariance.Graded

end


section

/-! The genuine Bott--Samelson stalk Hilbert coefficients satisfy the simple
reflection ascent recurrence. Both exactness and the degree-one kernel shift
were constructed integrally above; no KL character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance symmetricGrading_finite (n : ℤ) : Module.Finite ℝ (symmetricGrading basis n) :=
  inferInstanceAs (Module.Finite ℝ ((polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap))

 instance bottCoordinatePiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottCoordinatePiece cs basis l x n) := by
  classical
  exact piPiece_finite _ n

 instance bottStalkPiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottStalkPiece cs basis l x n) :=
  inferInstanceAs (Module.Finite ℝ (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x) n))

end
end KLInvariance.TitsSpace

end


section

/-! The genuine nonnegative polynomial generator character of word stalks,
with its convergent Hilbert-series interpretation. No KL identification is
asserted or included in the definition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPolynomialStalk_finrank (l : List I) (x : W) (n : ℤ) :
    Module.finrank ℝ ((bottPolynomialStalkData cs basis l x).piece n)=
      Module.finrank ℝ (bottStalkPiece cs basis l x n) :=
  LinearEquiv.finrank_map_eq
    (CoefficientChange.kEquiv (SymmetricAlgebra.equivMvPolynomial basis)
      (bottStalkData cs basis l x)) _

 theorem bottStalkCharacter_hasSum (l : List I) (x : W) {q : ℝ}
    (hq : 0<q) (hq1 : q<1) :
    HasSum (fun n : ℤ => (Module.finrank ℝ (bottStalkPiece cs basis l x n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q (bottStalkCharacter cs basis l x) *
        (1-q)⁻¹ ^ Fintype.card σ) := by
  have hh := (exists_nonnegativeBasis (k := ℝ) (σ := σ) (𝓜 := (bottPolynomialStalkData cs basis l x).piece)
    (bottPolynomialStalkData cs basis l x).nonneg).some.hasSum hq hq1
  apply hh.congr_fun
  intro n
  rw [bottPolynomialStalk_finrank]

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/

section

namespace KLInvariance.Hilbert
open Polynomial

 theorem numerator_unique (f : ℤ → ℕ) (F G : ℤ[X]) (D : ℝ → ℝ)
    (hD : ∀ q, 0<q → q<1 → D q≠0)
    (hF : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q F*D q))
    (hG : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q G*D q)) : F=G := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_ (Set.Ioo_infinite (by norm_num))
  intro q hq
  have he := (hF q hq.1 hq.2).unique (hG q hq.1 hq.2)
  change eval q (F.map (Int.castRingHom ℝ))=eval q (G.map (Int.castRingHom ℝ))
  simpa only [eval_map] using (mul_right_cancel₀ (hD q hq.1 hq.2) he)

end KLInvariance.Hilbert

end


section

/-! Genuine word stalk normalization and identification with the honest
Hecke word. This does not identify the indecomposable BMP character with KL. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_7
theorem bottStalkCharacter_zero (l : List I) (x : W)
    [Subsingleton (bottStalk cs l x)] : bottStalkCharacter cs basis l x=0 := by
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · intro q _ _
    simpa only [Module.finrank_zero_of_subsingleton,Nat.cast_zero,zero_mul,Polynomial.eval₂_zero] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)

omit [Fintype σ] in
 theorem bottTopPolynomialEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) (hs : s∈bottStalkPiece cs basis l (cs.wordProd l) n) :
    bottTopPolynomialEquiv cs basis l hl s∈polynomialGrading ℝ σ n := by
  apply (mem_symmetricGrading basis n _).mp
  exact (bottTopStalkEquiv_homogeneous cs basis l hl n s).mpr hs

 theorem bottStalkCharacter_top (l : List I) (hl : cs.IsReduced l) :
    bottStalkCharacter cs basis l (cs.wordProd l)=1 := by
  have hd (n : ℤ) : Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)=
      Module.finrank ℝ (polynomialGrading ℝ σ n) := by
    have hh := finrank_homogeneousEquiv (bottStalkPiece cs basis l (cs.wordProd l))
      (polynomialGrading ℝ σ) (bottTopPolynomialEquiv cs basis l hl) 0
      (fun n s hs => by simpa only [add_zero] using bottTopPolynomialEquiv_homogeneous cs basis l hl n s hs) n
    have hz : n-(0:ℤ)=n := Int.sub_zero n
    rw [hz] at hh
    exact hh.symm
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.wordProd l)
  · intro q hq hq1
    simpa only [hd,Polynomial.eval₂_one,one_mul] using Hilbert.hasSum_polynomial ℝ σ hq.le hq1

 theorem bottStalkCharacter_nil_oai (x : W) :
    bottStalkCharacter cs basis [] x=if x=1 then 1 else 0 := by
  classical
  by_cases hx : x=1
  · subst x
    simpa using bottStalkCharacter_top cs basis [] (by simp [CoxeterSystem.IsReduced])
  · let := bottStalk_nil_subsingleton cs x hx
    rw [ite_eq_right hx]
    exact bottStalkCharacter_zero cs basis [] x

end
end KLInvariance.TitsSpace

end


end OAI
end

theorem solution.{u} : type_of% @OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil_oai.{u} := @OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil_oai.{u}
