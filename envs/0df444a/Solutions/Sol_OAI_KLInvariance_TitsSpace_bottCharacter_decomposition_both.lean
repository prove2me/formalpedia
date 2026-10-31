-- Prove2me | solution 1 for OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:58:37.176124+00:00
-- url     : https://prove2.me/submissions/3c67850a-d481-4d00-869e-e386e3755961

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K024

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i}

lemma pi_compatible (B : ι → Sheaf.{u,v,w,z} (R := R) G) (Ω : Set V)
    (f : (pi B).Assignment) :
    (pi B).CompatibleOn Ω f ↔ ∀ i, (B i).CompatibleOn Ω (fun x => f x i) := by
  constructor
  · intro h i e hs ht
    exact congrFun (h e hs ht) i
  · intro h e hs ht
    funext i
    exact h i e hs ht

lemma pi_generated (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Generated) : (pi B).Generated := by
  intro x v
  classical
  choose f hf hfx using fun i => h i x (v i)
  exact ⟨fun y i => f i y,(pi_compatible B Set.univ _).mpr hf,funext hfx⟩

lemma pi_flabby (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Flabby) : (pi B).Flabby := by
  intro Ω hΩ f hf
  classical
  choose g hg hgf using fun i => h i Ω hΩ (fun x => f x i) ((pi_compatible B Ω f).mp hf i)
  exact ⟨fun y i => g i y,(pi_compatible B Set.univ _).mpr hg,fun x hx => funext (fun i => hgf i x hx)⟩

lemma pi_kernel_iff (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V)
    (f : (pi B).vertex x) :
    f ∈ LinearMap.ker ((pi B).stalkMap x) ↔ ∀ i, f i ∈ LinearMap.ker ((B i).stalkMap x) := by
  constructor
  · intro h i
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact congrFun (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩) i
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e i
    rcases e with ⟨e,he⟩
    subst x
    exact congrFun (LinearMap.mem_ker.mp (h i)) ⟨e,rfl⟩

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i} [Fintype ι]

lemma pi_minimal (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (h : ∀ i, LinearMap.ker ((B i).stalkMap x) ≤ I • (⊤ : Submodule R ((B i).vertex x))) :
    LinearMap.ker ((pi B).stalkMap x) ≤ I • (⊤ : Submodule R ((pi B).vertex x)) := by
  intro f hf
  exact LocalCover.pi_mem_ideal_smul (fun i => (B i).vertex x) I f
    (fun i => h i ((pi_kernel_iff B x f).mp hf i))

end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

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
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

lemma prod_generated (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Generated) (hC : C.Generated) : (prod B C).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hB x v.1
  obtain ⟨g,hg,hgx⟩ := hC x v.2
  exact ⟨fun y => (f y,g y),fun e hs ht => Prod.ext (hf e hs ht) (hg e hs ht),Prod.ext hfx hgx⟩

lemma prod_flabby (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Flabby) (hC : C.Flabby) : (prod B C).Flabby := by
  intro U hU f hf
  obtain ⟨g,hg,hgf⟩ := hB U hU (fun y => (f y).1) (fun e hs ht => congrArg Prod.fst (hf e hs ht))
  obtain ⟨t,ht,htf⟩ := hC U hU (fun y => (f y).2) (fun e hs htt => congrArg Prod.snd (hf e hs htt))
  exact ⟨fun y => (g y,t y),fun e hs htt => Prod.ext (hg e hs htt) (ht e hs htt),
    fun y hy => Prod.ext (hgf y hy) (htf y hy)⟩

lemma prod_upperQuotient (B C : Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) : (prod B C).UpperQuotient α := by
  intro e
  refine ⟨?_,?_⟩
  · intro v
    obtain ⟨b,hb⟩ := (hB e).1 v.1
    obtain ⟨c,hc⟩ := (hC e).1 v.2
    exact ⟨(b,c),Prod.ext hb hc⟩
  · intro v
    constructor
    · intro h
      obtain ⟨b,hb⟩ := (hB e).2 v.1 |>.mp (congrArg Prod.fst h)
      obtain ⟨c,hc⟩ := (hC e).2 v.2 |>.mp (congrArg Prod.snd h)
      exact ⟨(b,c),Prod.ext hb hc⟩
    · rintro ⟨⟨b,c⟩,rfl⟩
      exact Prod.ext ((hB e).2 _ |>.mpr ⟨b,rfl⟩) ((hC e).2 _ |>.mpr ⟨c,rfl⟩)

lemma pi_upperQuotient {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : ∀ i, (B i).UpperQuotient α) : (pi B).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose b hb using fun i => (hB i e).1 (v i)
    exact ⟨b,funext hb⟩
  · intro v
    constructor
    · intro h
      choose b hb using fun i => (hB i e).2 (v i) |>.mp (congrFun h i)
      exact ⟨b,funext hb⟩
    · rintro ⟨b,rfl⟩
      funext i
      exact (hB i e).2 _ |>.mpr ⟨b i,rfl⟩

lemma prod_kernel_iff (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (v : (prod B C).vertex x) :
    v ∈ LinearMap.ker ((prod B C).stalkMap x) ↔
      v.1 ∈ LinearMap.ker (B.stalkMap x) ∧ v.2 ∈ LinearMap.ker (C.stalkMap x) := by
  constructor
  · intro h
    constructor <;> apply LinearMap.mem_ker.mpr <;> funext e
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.fst (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.snd (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
  · rintro ⟨hB,hC⟩
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact Prod.ext (congrFun (LinearMap.mem_ker.mp hB) ⟨e,rfl⟩)
      (congrFun (LinearMap.mem_ker.mp hC) ⟨e,rfl⟩)

lemma prod_minimal (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (hB : LinearMap.ker (B.stalkMap x) ≤ I • (⊤ : Submodule R (B.vertex x)))
    (hC : LinearMap.ker (C.stalkMap x) ≤ I • (⊤ : Submodule R (C.vertex x))) :
    LinearMap.ker ((prod B C).stalkMap x) ≤ I • (⊤ : Submodule R ((prod B C).vertex x)) := by
  intro v hv
  obtain ⟨hvB,hvC⟩ := (prod_kernel_iff B C x v).mp hv
  have h (M N : Type z) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (f : M →ₗ[R] N) : (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hb := h _ _ (LinearMap.inl R (B.vertex x) (C.vertex x)) ⟨v.1,hB hvB,rfl⟩
  have hc := h _ _ (LinearMap.inr R (B.vertex x) (C.vertex x)) ⟨v.2,hC hvC,rfl⟩
  have heq : (v.1,0) + (0,v.2) = v := Prod.ext (add_zero _) (zero_add _)
  have hh := (I • (⊤ : Submodule R ((prod B C).vertex x))).add_mem hb hc
  change (v.1,0) + (0,v.2) ∈ I • (⊤ : Submodule R ((prod B C).vertex x)) at hh
  exact heq ▸ hh

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Finite sums of honest shifted normalized boundary models. A model family
is data for the decomposition lemma, not an assumption of the KL main. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}

namespace ModelSum
variable {hneg} {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {U : Set V} {B : GradedSheaf (𝓐 := 𝓐) G}

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
lemma mono {O : V → GradedSheaf (𝓐 := 𝓐) G} (h : ModelSum O U B)
    {T : Set V} (hUT : U ⊆ T) : ModelSum O T B := by
  induction h with
  | zero => exact .zero
  | add _ c hc n d ih => exact .add ih c (hUT hc) n d

lemma quotient (h : ModelSum O.sheaf U B) : B.UpperQuotient α := by
  induction h with
  | zero =>
    intro e
    exact ⟨fun v => ⟨0,Subsingleton.elim _ _⟩,fun v => ⟨fun _ => ⟨0,Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩⟩
  | @add C _ c _ n d ih =>
    exact Sheaf.prod_upperQuotient C.forget (Sheaf.pi (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget)) α ih
      (Sheaf.pi_upperQuotient (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget) α (fun _ => O.quotient c))

lemma generated (h : ModelSum O.sheaf U B) : B.forget.Generated := by
  induction h with
  | zero =>
    intro x v
    let : Subsingleton ((GradedSheaf.zero (𝓐 := 𝓐) (G := G)).forget.vertex x) := zeroVertex_subsingleton (𝓐 := 𝓐) (G := G) x
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩
  | add _ c _ n d ih => exact Sheaf.prod_generated _ _ ih (Sheaf.pi_generated _ (fun _ => O.generated c))

lemma flabby (h : ModelSum O.sheaf U B) : B.forget.Flabby := by
  induction h with
  | zero => exact fun U _ f _ => ⟨f,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | add _ c _ n d ih => exact Sheaf.prod_flabby _ _ ih (Sheaf.pi_flabby _ (fun _ => O.flabby c))

lemma minimal (h : ModelSum O.sheaf U B) (x : V) (hx : x ∉ U) : B.KernelMinimal x := by
  induction h with
  | zero =>
    apply (GradedSheaf.zero.kernelMinimal_iff x).mpr
    intro v _
    let : Subsingleton ((GradedSheaf.zero (𝓐 := 𝓐) (G := G)).forget.vertex x) := zeroVertex_subsingleton (𝓐 := 𝓐) (G := G) x
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  | @add C _ c hc n d ih =>
    apply ((prod C (pi (fun i => (O.sheaf c).shift (d i)))).kernelMinimal_iff x).mpr
    exact Sheaf.prod_minimal C.forget (Sheaf.pi (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget)) x _ ((C.kernelMinimal_iff x).mp ih)
      (Sheaf.pi_minimal (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget) x _ (fun _ =>
        ((O.sheaf c).kernelMinimal_iff x).mp (O.minimal c x (fun he => hx (he ▸ hc)))))

end ModelSum
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
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

lemma polynomial_eq (c : NonnegativeBasis (σ := σ) 𝓜) : b.polynomial = c.polynomial := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {q | Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))} := by
    intro q hq
    have h := (b.hasSum hq.1 hq.2).unique (c.hasSum hq.1 hq.2)
    have hne : (1-q)⁻¹ ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq.2)))
    change Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))
    simpa only [Polynomial.eval_map] using mul_right_cancel₀ hne h
  exact Set.Infinite.mono hsub (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))

end NonnegativeBasis

lemma character_eq [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥)
    (b : NonnegativeBasis (σ := σ) 𝓜) : character (σ := σ) 𝓜 hneg = b.polynomial :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial_eq b

end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {M : Type um} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
noncomputable section

omit [IsScalarTower k A M] in
 theorem basis_coordinates_graded {ι : Type ui} [Fintype ι]
    (b : Module.Basis ι A M) (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))
    (n : ℤ) (m : M) (hm : m ∈ 𝓜 n) :
    ∀ i, b.equivFun m i ∈ 𝓐 (n-d i) := by
  classical
  let : DirectSum.Decomposition (shiftedPiece 𝓐 d) := (shifted_isInternal 𝓐 d).chooseDecomposition
  have he : ∀ n v, v ∈ shiftedPiece 𝓐 d n → b.equivFun.symm v ∈ 𝓜 n := by
    intro n v hv
    rw [b.equivFun_symm_apply]
    apply Submodule.sum_mem
    intro i _
    simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)
  have hh := map_component (shiftedPiece 𝓐 d) 𝓜 b.equivFun.symm.toLinearMap 0
    (by simpa using he) n (b.equivFun m)
  simp only [sub_zero,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] at hh
  rw [show component 𝓜 n m=m from DirectSum.decompose_of_mem_same 𝓜 hm] at hh
  have hc : component (shiftedPiece 𝓐 d) n (b.equivFun m)=b.equivFun m := by
    apply b.equivFun.symm.injective
    exact hh.symm.trans (b.equivFun.symm_apply_apply m).symm
  rw [← hc]
  exact (DirectSum.decompose (shiftedPiece 𝓐 d) (b.equivFun m) n).property

end
end KLInvariance.Graded

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem exists_equiv_shiftedUnits (F : ModuleData.{uk,ua,um} 𝓐) [Module.Free A F] :
    ∃ (n : ℕ) (d : ULift.{um} (Fin n) → ℕ)
      (e : F ≃ₗ[A] pi (fun i : ULift.{um} (Fin n) => (unit hneg).shift (d i))),
      ∀ m v, v ∈ F.piece m → e v ∈
        (pi (fun i : ULift.{um} (Fin n) => (unit hneg).shift (d i))).piece m := by
  classical
  obtain ⟨ι,hι,b0,hd0⟩ := exists_homogeneous_basis_connected 𝓐 F.piece hneg hzero 0 F.nonneg
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι
  let J := ULift.{um} (Fin n)
  let re : ι ≃ J := (Fintype.equivFin ι).trans Equiv.ulift.symm
  let b := b0.reindex re
  choose dz hdz using hd0
  let d : J → ℕ := fun i => (dz (re.symm i)).toNat
  have hd (i : J) : b i ∈ F.piece (d i : ℤ) := by
    have hz : 0 ≤ dz (re.symm i) := by
      by_contra h
      have he : b0 (re.symm i)=0 := by
        simpa only [F.nonneg _ (lt_of_not_ge h),Submodule.mem_bot] using hdz (re.symm i)
      exact b0.ne_zero (re.symm i) he
    simpa only [b,Module.Basis.reindex_apply,d,Int.toNat_of_nonneg hz] using hdz (re.symm i)
  let e : F ≃ₗ[A] pi (fun i : J => (unit hneg).shift (d i)) :=
    { toFun v i _ := b.equivFun v i
      invFun v := b.equivFun.symm (fun i => v i PUnit.unit)
      left_inv v := b.equivFun.symm_apply_apply v
      right_inv v := by
        funext i j
        change b.equivFun (b.equivFun.symm (fun i => v i PUnit.unit)) i=v i j
        rw [LinearEquiv.apply_symm_apply]
      map_add' v w := by funext i j; exact congrFun (b.equivFun.map_add v w) i
      map_smul' a v := by funext i j; exact congrFun (b.equivFun.map_smul a v) i }
  refine ⟨n,d,e,?_⟩
  intro m v hv i _ j
  change b.equivFun v i ∈ 𝓐 (m-(d i : ℤ)-0)
  rw [sub_zero]
  exact basis_coordinates_graded F.piece b (fun i => (d i : ℤ)) hd m v hv i

end
end KLInvariance.Graded.ModuleData

end


section

/-! A minimal graded free cover splits out of every finite graded free cover.
The residual kernel is genuinely graded free over the connected coefficient ring.
This is the local step for decomposing actual flabby word sheaves. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem exists_minimalCover_split {T F : ModuleData.{uk,ua,um} 𝓐}
    (C : MinimalCover T) [Module.Free A F]
    (f : Hom F T) (hf : Function.Surjective f.map) :
    ∃ (g : Hom F C.source) (h : Hom C.source F),
      C.hom.map.comp g.map = f.map ∧ g.map.comp h.map = LinearMap.id := by
  let : Module.Free A C.source := C.free
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective f
  obtain ⟨t,ht⟩ := exists_hom_lift hneg hzero f hf C.hom
  have hgt : Function.Bijective (g.comp t).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-g.map (t.map v))=0
    rw [map_sub,← LinearMap.comp_apply,hg,← LinearMap.comp_apply,ht,sub_self]
  refine ⟨g,t.comp ((g.comp t).inverse hgt),hg,?_⟩
  ext v
  exact (g.comp t).map_inverse hgt v

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] [IsDomain A] in
 theorem Hom.splitEquiv_graded {F C : ModuleData.{uk,ua,um} 𝓐}
    (g : Hom F C) (h : Hom C F) (hgh : g.map.comp h.map = LinearMap.id)
    (n : ℤ) (v : F) (hv : v ∈ F.piece n) :
    g.splitEquiv h hgh v ∈ (prod C (kernel g)).piece n := by
  constructor
  · exact g.graded n v hv
  · exact Submodule.sub_mem _ hv (h.graded n _ (g.graded n v hv))

include hneg hzero in
 theorem Hom.kernel_free_of_split {F C : ModuleData.{uk,ua,um} 𝓐}
    [Module.Free A F] (g : Hom F C) (h : Hom C F)
    (hgh : g.map.comp h.map = LinearMap.id) : Module.Free A (kernel g) := by
  let e := g.splitEquiv h hgh
  let p : F →ₗ[A] kernel g := (LinearMap.snd A C (kernel g)).comp e.toLinearMap
  have hp : p.comp g.map.ker.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((v : F) - h.map (g.map v))=v
    rw [LinearMap.mem_ker.mp v.property,map_zero,sub_zero]
  let : Module.Projective A (kernel g) := Module.Projective.of_split g.map.ker.subtype p hp
  obtain ⟨ι,hι,b,_⟩ := exists_homogeneous_basis_connected 𝓐 (kernel g).piece
    hneg hzero 0 (kernel g).nonneg
  exact Module.Free.of_basis b

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem split_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hCmin : C.KernelMinimal x) :
    ∃ (g : ModuleData.Hom (B.vertex x) (C.vertex x))
      (e : B.vertex x ≃ₗ[A] C.vertex x × ModuleData.kernel g),
      Module.Free A (ModuleData.kernel g) ∧
      (∀ n v, v ∈ (B.vertex x).piece n →
        e v ∈ (ModuleData.prod (C.vertex x) (ModuleData.kernel g)).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v).1 := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let p : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hps : Function.Surjective p.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hpm : LinearMap.ker p.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : p.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,p,hps,hpm⟩
  let : Module.Free A (B.vertex x) := hBfree
  obtain ⟨g,h,hg,hgh⟩ := ModuleData.exists_minimalCover_split hneg hzero D f hfs
  refine ⟨g,g.splitEquiv h hgh,g.kernel_free_of_split hneg hzero h hgh,
    g.splitEquiv_graded h hgh,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hg v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype E] {G : OrderedGraph V E}
  {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

include hzero in
 theorem extend_modelSum {U : Set V} (hU : IsUpperSet U)
    (hC : ModelSum O.sheaf U C) (j : OnIso B C U)
    (hBq : B.UpperQuotient α) (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U)
    [Module.Free A (B.vertex x)] :
    ∃ D : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf (insert x U) D ∧ Nonempty (OnIso B D (insert x U)) := by
  classical
  obtain ⟨g,jv,hfree,hjvgrade,hjv⟩ := (j.toOnIso.above x hmax).split_stalk_graded hneg hzero
    (fun e he => j.edge_graded e (hmax he)) inferInstance (hC.free O x)
    hBf hBg (hC.flabby O) (hC.generated O) (hC.minimal O x hx)
  let := hfree
  obtain ⟨n,d,jq0,hjq0⟩ := ModuleData.exists_equiv_shiftedUnits hneg hzero (ModuleData.kernel g)
  let S : GradedSheaf (𝓐 := 𝓐) G := pi (fun i : ULift.{um} (Fin n) => (O.sheaf x).shift (d i))
  let jq1 : ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i))
      ≃ₗ[A] S.vertex x := LinearEquiv.piCongrRight (fun _ => (O.top x).symm)
  have hjq1 (m : ℤ) (v : ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i)))
      (hv : v ∈ (ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i))).piece m) :
      jq1 v ∈ (S.vertex x).piece m := by
    intro i _
    let t : ModuleData.Hom ((O.sheaf x).vertex x) (ModuleData.unit hneg) :=
      ⟨(O.top x).toLinearMap,O.top_graded x⟩
    apply t.mem_of_map_mem (O.top x).injective (m-(d i : ℤ))
    change O.top x ((O.top x).symm (v i)) ∈ (ModuleData.unit hneg).piece (m-(d i : ℤ))
    exact ((O.top x).apply_symm_apply (v i)).symm ▸ hv i (Set.mem_univ i)
  let jq := jq0.trans jq1
  let jv' : B.vertex x ≃ₗ[A] (prod C S).vertex x :=
    jv.trans (LinearEquiv.prodCongr (LinearEquiv.refl A (C.vertex x)) jq)
  have hjv' (m : ℤ) (v : B.vertex x) (hv : v ∈ (B.vertex x).piece m) :
      jv' v ∈ ((prod C S).vertex x).piece m :=
    ⟨(hjvgrade m v hv).1,hjq1 m _ (hjq0 m _ (hjvgrade m v hv).2)⟩
  have hSV (y : V) (hy : y ∈ U) : Subsingleton (S.vertex y) := by
    let := O.support x y (fun hyx => hx (hU hyx hy))
    exact inferInstanceAs (Subsingleton (ULift.{um} (Fin n) → (O.sheaf x).vertex y))
  have hSE (e : E) (he : G.target e ∈ U) : Subsingleton (S.edge e) := by
    let := O.support x (G.target e) (fun h => hx (hU h he))
    let : Subsingleton ((O.sheaf x).edge e) := (O.quotient x e).1.subsingleton
    exact inferInstanceAs (Subsingleton (ULift.{um} (Fin n) → (O.sheaf x).edge e))
  let jj : OnIso B (prod C S) U := j.prodZero S hSV hSE
  have hsum : ModelSum O.sheaf (insert x U) (prod C S) :=
    .add (hC.mono (Set.subset_insert x U)) x (Set.mem_insert x U) n d
  have hout : ∀ e (he : G.source e = x) v,
      jj.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.forget.lower e v) = (prod C S).forget.lower e
          (Sheaf.castStalkIso B.forget (prod C S).forget he.symm jv' v) := by
    intro e he v
    subst x
    apply Prod.ext
    · exact congrFun (hjv v) ⟨e,rfl⟩
    · let := hSE e (hmax (G.increasing e))
      exact Subsingleton.elim _ _
  exact ⟨prod C S,hsum,⟨jj.extend hU x hx hmax α hBq (hsum.quotient O) jv' hjv' hout⟩⟩

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype E] {G : OrderedGraph V E}
  {α : E → A} (O : BoundaryModels hneg (G := G) α)
  (B : GradedSheaf (𝓐 := 𝓐) G)

include hzero in
/-- Finite graded decomposition with actual nonnegative shifts. -/
theorem exists_modelSumIso [Finite V]
    (hBfree : ∀ x, Module.Free A (B.vertex x))
    (hBq : B.UpperQuotient α) (hBf : B.forget.Flabby) (hBg : B.forget.Generated) :
    ∃ C : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf Set.univ C ∧ Nonempty (Iso B C) := by
  classical
  let := Fintype.ofFinite V
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ C : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf ((s : Set V)ᶜ) C → OnIso B C ((s : Set V)ᶜ) →
      ∃ D : GradedSheaf (𝓐 := 𝓐) G,
        ModelSum O.sheaf Set.univ D ∧ Nonempty (Iso B D) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU C hC j
      by_cases hs : s = ∅
      · subst s
        have hh : ((∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
        exact ⟨C,hh ▸ hC,⟨OnIso.ofUniv (hh ▸ j)⟩⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        obtain ⟨D,hD,⟨jj⟩⟩ := extend_modelSum hzero O hU hC j hBq hBf hBg x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') D (heq ▸ hD) (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : OnIso B zero (∅ : Set V) :=
    ⟨⟨fun x hx => False.elim hx,fun e he => False.elim he,
      fun e hs => False.elim hs,fun e ht => False.elim ht⟩,
      fun x hx => False.elim hx,fun e he => False.elim he⟩
  have hinit := h Finset.univ
  rw [hset] at hinit
  exact hinit isUpperSet_empty zero .zero hj

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Graded linear equivalence preserves the genuine free-module character.
This does not assert its identification with any KL polynomial. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ)}

 theorem character_eq_of_gradedEquiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N] (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n) :
    character (σ := σ) M.piece M.nonneg = character (σ := σ) N.piece N.nonneg := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [character_eq M.piece M.nonneg b,
    character_eq N.piece N.nonneg (mapNonnegativeBasis e he b)]
  rfl

end KLInvariance.Graded.ModuleData

end


section

/-! Honest polynomial characters commute with actual finite graded sums and
nonnegative shifts. No Hecke or KL identification enters these lemmas. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 theorem char_shift [Module.Free (MvPolynomial σ k) M] (d : ℕ) :
    (M.shift d).char=X^d*M.char := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.shiftedBasis b d),char,character_eq _ _ b]
  change (∑ i : b.index, (X : Polynomial ℤ) ^ (b.degree i+d)) = X^d*∑ i, X^b.degree i
  simp only [pow_add,mul_comm,Finset.mul_sum]

 theorem char_prod [Module.Free (MvPolynomial σ k) M] [Module.Free (MvPolynomial σ k) N] :
    (M.prod N).char=M.char+N.char := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  let c := (exists_nonnegativeBasis (σ := σ) N.piece N.nonneg).some
  rw [char,character_eq _ _ (M.productBasis N b c),char,character_eq _ _ b,
    char,character_eq _ _ c]
  change (∑ i : b.index ⊕ c.index, (X : Polynomial ℤ)^Sum.elim b.degree c.degree i) =
    (∑ i : b.index, X^b.degree i)+(∑ i : c.index, X^c.degree i)
  exact Fintype.sum_sum_type (fun i => (X : Polynomial ℤ)^Sum.elim b.degree c.degree i)

 theorem char_pi {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    [∀ i, Module.Free (MvPolynomial σ k) (F i)] :
    (pi F).char=∑ i, (F i).char := by
  let b := fun i => (exists_nonnegativeBasis (σ := σ) (F i).piece (F i).nonneg).some
  rw [char,character_eq _ _ (piBasis F b)]
  change (∑ i : Σ j, (b j).index, (X : Polynomial ℤ)^(b i.1).degree i.2) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (character_eq (F i).piece (F i).nonneg (b i)).symm

 theorem char_zero [Subsingleton M] [Module.Free (MvPolynomial σ k) M] : M.char=0 := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  have : IsEmpty b.index := ⟨fun i => b.basis.ne_zero i (Subsingleton.elim _ _)⟩
  rw [char,character_eq _ _ b]
  simp [NonnegativeBasis.polynomial]

end
end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottHeadKernelPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottHeadPairAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottHeadPairModule _root_.OAI.KLInvariance.TitsSpace.bottHeadRightKernelPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottPiece_graded _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree _root_.OAI.KLInvariance.TitsSpace.bottRealModule _root_.OAI.KLInvariance.TitsSpace.bottRealTower _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.bottStalkFinite _root_.OAI.KLInvariance.TitsSpace.bottStalkFree _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_decomposition _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_graded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_1
theorem boundaryModels_character (c x : Interval cs 1 b) :
    GradedSheaf.freeStalkChar ((boundaryModels cs b basis).sheaf c)
      ((boundaryModels cs b basis).free c) x=lowerCharacter cs b basis c x := by
  let _ := (boundaryModels cs b basis).free c x
  by_cases hx : x ≤ c
  · rw [lowerCharacter,dite_eq_left hx]
    let B := lowerIntervalBoundary cs b basis c
    let _ := B.sheaf.lowerExtend_free B.free x
    let _ := (boundarySheaf cs 1 c.val basis (one_bruhat cs c.val)).free ⟨x.val,x.property.1,hx⟩
    exact ModuleData.character_eq_of_gradedEquiv (B.sheaf.lowerExtendVertex ⟨x,hx⟩)
      (B.sheaf.lowerExtendVertex_graded ⟨x,hx⟩)
  · rw [lowerCharacter,dite_eq_right hx]
    let _ := (boundaryModels cs b basis).support c x hx
    exact ModuleData.char_zero _

end
end KLInvariance.BruhatGraph

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


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

/-! Positive triangular decomposition of the honest word's character into
actual BMP stalk characters. The KL identification is not assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPolynomialSheaf_flabby (l : List I) (hl : cs.IsReduced l) :
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)).forget.Flabby :=
  GradedSheaf.coefficientChange_flabby _ _ _ (bottProjectionSheaf_flabby cs l hl)

 theorem bottPolynomialSheaf_character (l : List I) (u b : W) (x : Interval cs u b) :
    GradedSheaf.freeStalkChar (bottPolynomialSheaf cs basis l u b)
      (bottPolynomialSheaf_free cs basis l u b) x=bottStalkCharacter cs basis l x.val := rfl

end
end KLInvariance.TitsSpace

end


section

/-! Genuine polynomial reflection from a homogeneous perfect duality. The
nonnegative lattice supplies a weak degree bound, not the strict KL bound. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 theorem char_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    N.char=Polynomial.reflect l M.char := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.reflectedBasis N e l he c),char,character_eq _ _ c]
  change (∑ i : c.index, (X : Polynomial ℤ)^(l-c.degree i))=
    Polynomial.reflect l (∑ i : c.index, X^c.degree i)
  have hs (s : Finset c.index) : Polynomial.reflect l (∑ i∈s, (X : Polynomial ℤ)^c.degree i)=
      ∑ i∈s, Polynomial.reflect l (X^c.degree i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha,ih]
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.reflect_monomial,Polynomial.revAt_le (M.degree_le_of_dual_equiv N e l he c i)]

end
end KLInvariance.Graded.ModuleData

end


section


namespace KLInvariance.MomentGraph.GradedSheaf
open Module _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E] [DecidableEq V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)
  [IsNoetherianRing A] [IsDomain A]
  [∀ x, Module.IsTorsionFree A (B.forget.vertex x)]
  (α : E → A) (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (p : B.forget.sections Set.univ ≃ₗ[A] Dual A (B.forget.sections Set.univ))
  (hbalanced : ∀ x m n,
    p (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x m) n =
    p m (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x n))
noncomputable section

 theorem dualToSupport_homogeneous (l : ℤ)
    (hp : ∀ i j (m n : B.sections Set.univ),
      m ∈ (B.sections Set.univ).piece i → n ∈ (B.sections Set.univ).piece j →
      p m n ∈ 𝓐 (i+j-l))
    (x : V) (r : ℤ) (lam : Dual A (B.vertex x))
    (hlam : ∀ j (v : B.vertex x), v ∈ (B.vertex x).piece j → lam v ∈ 𝓐 (j+r)) :
    (IntegralSupport.dualToSupport (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha))
      (Sheaf.labelProduct_ne_zero α hα) p hbalanced x lam).val ∈
        (B.sections Set.univ).piece (r+l) := by
  apply perfect_inverse_of_homogeneous_functional 𝓐 (B.sections Set.univ).piece p l hp r
  intro j n hn
  exact hlam j (n.val x) (hn x (Set.mem_univ x))

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]

/-- Cancellation of an injective homogeneous scalar action includes the
inverse grading shift. It does not require the scalar to be a unit. -/
 theorem mem_of_homogeneous_smul (d : ℤ) (a : A) (ha : a ∈ 𝓐 d)
    (hinj : Function.Injective (fun m : M => a • m))
    (n : ℤ) (m : M) (hm : a • m ∈ 𝓜 n) : m ∈ 𝓜 (n-d) := by
  have hc : component 𝓜 (n-d) m = m := by
    apply hinj
    change a • component 𝓜 (n-d) m = a • m
    rw [← component_homogeneous_smul 𝓐 𝓜 d a ha]
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  rw [← hc]
  exact (DirectSum.decompose 𝓜 m (n-d)).property

end KLInvariance.Graded

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

omit [Fintype (Interval cs u b)] in
 theorem incomingProduct_homogeneous (x : Interval cs u b) :
    Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x ∈
      polynomialGrading ℝ σ ((Sheaf.incoming (G := graph cs u b) x).card : ℤ) := by
  simpa only [Sheaf.incomingProduct,Finset.sum_const,Int.natCast_one,mul_one,nsmul_eq_mul] using
    SetLike.prod_mem_graded (polynomialGrading ℝ σ) (fun _ : Edge cs u b => (1 : ℤ))
      (polynomialLabel cs u b basis)
      (F := Sheaf.incoming (G := graph cs u b) x)
      (fun e _ => polynomialLabel_homogeneous cs u b basis e)

end
end KLInvariance.BruhatGraph

end


section

/-! The degree of the actual incoming root product on [1,b].  This is not
asserted for truncated intervals with arbitrary bottom. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
noncomputable section

 theorem incoming_card [Fintype (Edge cs 1 b)] [DecidableEq (Interval cs 1 b)]
    (x : Interval cs 1 b) : (Sheaf.incoming (G := graph cs 1 b) x).card = cs.length x.val := by
  classical
  calc
    _ = Nat.card {e : Edge cs 1 b // target cs 1 b e = x} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    _ = Nat.card {t : W // cs.IsLeftInversion x.val t} := Nat.card_congr (incomingEquivInversions cs b x)
    _ = Nat.card (RootInversions M cs x.val) := Nat.card_congr (rootInversionEquiv M cs x.val).symm
    _ = cs.length x.val := card_rootInversions M cs x.val

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Integral costalk duality only uses free stalks, the genuine edge quotients,
generation and a perfect support-orthogonal section form. No top/minimality or
KL character assumption is needed. This extension applies to genuine words. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))

namespace FreeSheaf
variable (B : FreeSheaf cs u b basis)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 variable [Fintype σ] [Fintype (Interval cs u b)]

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis B d x).symm lam).val ∈
      (B.sheaf.vertex x).piece
        (r+l-(Sheaf.incoming (G := graph cs u b) x).card) := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  let S := B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
    (polynomialLabel_ne_zero cs u b basis)
    (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
    d.pairing d.balanced B.generated x
  have hs : (S.symm lam).val ∈ (B.sheaf.sections Set.univ).piece (r+l) := by
    exact B.sheaf.dualToSupport_homogeneous (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced l hd x r lam hlam
  have hv := hs x (Set.mem_univ x)
  have he : (S.symm lam).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x •
      ((costalkEquivDual cs u b basis B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis B x)
        ((kernelEquivSingleSupport cs u b basis B x).symm (S.symm lam))).val.val x
    rw [LinearEquiv.apply_symm_apply]
  change (S.symm lam).val.val x ∈ (B.sheaf.vertex x).piece (r+l) at hv
  rw [he] at hv
  apply mem_of_homogeneous_smul (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
    ((Sheaf.incoming (G := graph cs u b) x).card : ℤ)
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x)
    (incomingProduct_homogeneous cs u b basis x) _ (r+l) _ hv
  let _ := B.free x
  exact smul_right_injective _ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)

end
end FreeSheaf
end KLInvariance.BruhatGraph

end


section

/-! Actual full upward kernels commute with finite graded sums, shifts and
sheaf isomorphisms. No freeness is inferred without a free model. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 theorem kernelProdEquiv_graded (B C : GradedSheaf (𝓐 := 𝓐) G) (x : V)
    (n : ℤ) (v : kernelData (prod B C) x) (hv : v∈(kernelData (prod B C) x).piece n) :
    kernelProdEquiv B C x v∈((kernelData B x).prod (kernelData C x)).piece n := hv

 theorem kernelPiEquiv_graded {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) (x : V)
    (n : ℤ) (v : kernelData (pi B) x) (hv : v∈(kernelData (pi B) x).piece n) :
    kernelPiEquiv B x v∈(ModuleData.pi (fun i => kernelData (B i) x)).piece n := hv

 theorem kernelShiftEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) (d : ℕ)
    (n : ℤ) (v : kernelData (B.shift d) x) (hv : v∈(kernelData (B.shift d) x).piece n) :
    kernelShiftEquiv B x d v∈((kernelData B x).shift d).piece n := hv

 theorem Iso.kernelEquiv_graded {B C : GradedSheaf (𝓐 := 𝓐) G} (j : Iso B C) (x : V)
    (n : ℤ) (v : kernelData B x) (hv : v∈(kernelData B x).piece n) :
    j.kernelEquiv x v∈(kernelData C x).piece n := j.vertex_graded x n v.val hv

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 theorem kernelChar_shift (B : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V) (d : ℕ)
    [Module.Free (MvPolynomial σ k) (kernelData B x)] :
    (kernelData (B.shift d) x).char=X^d*(kernelData B x).char := by
  rw [← ModuleData.char_shift _ d]
  exact ModuleData.character_eq_of_gradedEquiv (kernelShiftEquiv B x d)
    (kernelShiftEquiv_graded B x d)

 theorem kernelChar_prod (B C : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [Module.Free (MvPolynomial σ k) (kernelData B x)]
    [Module.Free (MvPolynomial σ k) (kernelData C x)] :
    (kernelData (prod B C) x).char=(kernelData B x).char+(kernelData C x).char := by
  rw [← ModuleData.char_prod]
  exact ModuleData.character_eq_of_gradedEquiv (kernelProdEquiv B C x)
    (kernelProdEquiv_graded B C x)

 theorem kernelChar_pi {ι : Type um} [Fintype ι]
    (B : ι → GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [∀ i, Module.Free (MvPolynomial σ k) (kernelData (B i) x)] :
    (kernelData (pi B) x).char=∑ i, (kernelData (B i) x).char := by
  rw [← ModuleData.char_pi]
  exact ModuleData.character_eq_of_gradedEquiv (kernelPiEquiv B x) (kernelPiEquiv_graded B x)

 theorem kernelChar_zero (x : V) :
    (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x).char=0 := by
  let : Subsingleton (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact ModuleData.char_zero _

 theorem ModelSum.character_both [Fintype V] {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (hk : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O.sheaf y) x))
    {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O.sheaf U B) :
    ∃ m : V → Polynomial ℤ, (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, freeStalkChar B (h.free O) x =
        ∑ y, m y*freeStalkChar (O.sheaf y) (O.free y) x) ∧
      (∀ x, freeKernelChar B (h.kernelFree hk) x =
        ∑ y, m y*freeKernelChar (O.sheaf y) (hk y) x) := by
  classical
  induction h with
  | zero =>
    refine ⟨0,by simp,?_,?_⟩
    · intro x
      change ((GradedSheaf.zero (𝓐 := polynomialGrading k σ) (G := G)).vertex x).char = _
      simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
      exact ModuleData.char_zero _
    · intro x
      change (kernelData (GradedSheaf.zero (𝓐 := polynomialGrading k σ) (G := G)) x).char = _
      simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
      exact kernelChar_zero (σ := σ) (G := G) x
  | @add B h c hc n d ih =>
    obtain ⟨m,hm,heq,hkeq⟩ := ih
    let a : Polynomial ℤ := ∑ i, X^(d i)
    have ha (r : ℕ) : 0 ≤ a.coeff r := by
      simp only [a,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
      exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    refine ⟨fun y => m y+if y=c then a else 0,?_,?_,?_⟩
    · intro y r
      rw [Polynomial.coeff_add]
      apply add_nonneg (hm y r)
      split
      · exact ha r
      · simp
    · intro x
      let _ := h.free O x
      let _ := O.free c x
      change ((B.vertex x).prod (ModuleData.pi (fun i => ((O.sheaf c).vertex x).shift (d i)))).char = _
      rw [ModuleData.char_prod,ModuleData.char_pi]
      simp only [ModuleData.char_shift]
      change freeStalkChar B (h.free O) x + _ = _
      rw [heq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
      rfl
    · intro x
      let _ := h.kernelFree hk x
      let _ := hk c x
      change (kernelData (prod B (pi (fun i => (O.sheaf c).shift (d i)))) x).char = _
      rw [kernelChar_prod,kernelChar_pi]
      simp only [kernelChar_shift]
      change freeKernelChar B (h.kernelFree hk) x + _ = _
      rw [hkeq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
      rfl

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph.FreeSheaf
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (B : FreeSheaf cs 1 b basis)
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 theorem kernelDual_homogeneous (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (x : Interval cs 1 b) (hn : cs.length x.val≤n) (r : ℤ)
    (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v∈(B.sheaf.vertex x).piece j →
      lam v∈polynomialGrading ℝ σ (j+r)) :
    kernelDual cs b basis B d x lam∈(GradedSheaf.kernelData B.sheaf x).piece
      (r+(n-cs.length x.val : ℕ)) := by
  have h := costalkEquivDual_inverse_homogeneous cs 1 b basis B d n hd x r lam hlam
  rw [incoming_card] at h
  change ((costalkEquivDual cs 1 b basis B d x).symm lam).val∈
    (B.sheaf.vertex x).piece (r+↑(n-cs.length x.val))
  have he : r+(n:ℤ)-cs.length x.val=r+↑(n-cs.length x.val) := by omega
  rwa [he] at h

 theorem kernel_character (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (hn : cs.length b≤n) (x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar B.sheaf (kernel_free cs b basis B d) x=
      Polynomial.reflect (n-cs.length x.val) (GradedSheaf.freeStalkChar B.sheaf B.free x) := by
  let := B.free x
  let := kernel_free cs b basis B d x
  exact ModuleData.char_of_dual_equiv _ _ (kernelDual cs b basis B d x) _
    (kernelDual_homogeneous cs b basis B d n hd x ((length_le_of_bruhat cs x.property.2).trans hn))

end
end KLInvariance.BruhatGraph.FreeSheaf

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteInterval
attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteEdges
attribute [local instance] OAI.KLInvariance.BruhatGraph.charDecEqC
theorem costalkCharacter_reflect (x : Interval cs 1 b) :
    costalkCharacter cs b basis x=Polynomial.reflect (rankDifference cs x.val b)
      (stalkCharacter cs 1 b basis (one_bruhat cs b) x) := by
  apply FreeSheaf.kernel_character cs b basis _ (boundaryFreeDuality cs b basis) (cs.length b) _ le_rfl x
  intro i j m a hm ha
  exact (boundaryPerfectPairing cs b basis).homogeneous i j m a
    (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K : Set V} {hK : IsLowerSet K}

 theorem lowerExtendKernelEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) (n : ℤ) (m : kernelData B.lowerExtend x.val)
    (hm : m∈(kernelData B.lowerExtend x.val).piece n) :
    B.lowerExtendKernelEquiv x m∈(kernelData B x).piece n :=
  B.lowerExtendVertex_graded x n m.val hm

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_2
theorem lowerKernelEquiv_graded (c x : Interval cs 1 b) (hx : x ≤ c)
    (n : ℤ) (v : GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x)
    (hv : v∈(GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x).piece n) :
    lowerKernelEquiv cs b basis c x hx v∈(GradedSheaf.kernelData
      (boundaryFreeSheaf cs c.val basis).sheaf ⟨x.val,x.property.1,hx⟩).piece n :=
  (lowerIntervalBoundary cs b basis c).sheaf.lowerExtendKernelEquiv_graded ⟨x,hx⟩ n v hv

 theorem boundaryModels_kernelCharacter (c x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar ((boundaryModels cs b basis).sheaf c)
      (boundaryModels_kernelFree cs b basis c) x=
      Polynomial.reflect (rankDifference cs x.val c.val) (lowerCharacter cs b basis c x) := by
  let := boundaryModels_kernelFree cs b basis c x
  by_cases hx : x ≤ c
  · rw [lowerCharacter,dite_eq_left hx,← costalkCharacter_reflect cs c.val basis ⟨x.val,x.property.1,hx⟩]
    let := boundaryKernelFree cs c.val basis ⟨x.val,x.property.1,hx⟩
    exact ModuleData.character_eq_of_gradedEquiv (lowerKernelEquiv cs b basis c x hx)
      (lowerKernelEquiv_graded cs b basis c x hx)
  · rw [lowerCharacter,dite_eq_right hx,Polynomial.reflect_zero]
    let := (boundaryModels cs b basis).support c x hx
    let : Subsingleton (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) :=
      ⟨fun v w => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ModuleData.char_zero _

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 theorem exists_character_decomposition [Fintype V] [Fintype E]
    {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (hk : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O.sheaf y) x))
    (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x))
    (hkb : ∀ x, Module.Free (MvPolynomial σ k) (kernelData B x))
    (hq : B.UpperQuotient α) (hfl : B.forget.Flabby) (hg : B.forget.Generated) :
    ∃ m : V → Polynomial ℤ, (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, freeStalkChar B hf x =
        ∑ y, m y*freeStalkChar (O.sheaf y) (O.free y) x) ∧
      (∀ x, freeKernelChar B hkb x =
        ∑ y, m y*freeKernelChar (O.sheaf y) (hk y) x) := by
  obtain ⟨C,hC,⟨j⟩⟩ := exists_modelSumIso (polynomialGrading_zero k σ) O B hf hq hfl hg
  obtain ⟨m,hm,heq,hkeq⟩ := hC.character_both O hk
  refine ⟨m,hm,fun x => ?_,fun x => ?_⟩
  · rw [← heq x]
    let _ := hf x
    let _ := hC.free O x
    exact ModuleData.character_eq_of_gradedEquiv (j.vertex x) (j.vertex_graded x)
  · rw [← hkeq x]
    let _ := hkb x
    let _ := hC.kernelFree hk x
    exact ModuleData.character_eq_of_gradedEquiv (j.kernelEquiv x) (j.kernelEquiv_graded x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottCharacter_decomposition_both_oai (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] :
    ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
      (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, bottStalkCharacter cs basis l x.val=
        ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x) ∧
      (∀ x, GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
        (bottKernelFree cs basis l hl) x=
        ∑ y, m y*Polynomial.reflect (rankDifference cs x.val y.val)
          (lowerCharacter cs (cs.wordProd l) basis y x)) := by
  classical
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  obtain ⟨m,hm,he,hk⟩ := GradedSheaf.exists_character_decomposition
    (boundaryModels cs (cs.wordProd l) basis) (boundaryModels_kernelFree cs (cs.wordProd l) basis)
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l)) (bottKernelFree cs basis l hl)
    (bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_flabby cs basis l hl) (bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l))
  refine ⟨m,hm,fun x => ?_,fun x => ?_⟩
  · simpa only [bottPolynomialSheaf_character,boundaryModels_character] using he x
  · simpa only [boundaryModels_kernelCharacter] using hk x

end
end KLInvariance.TitsSpace

end


end OAI
end

theorem solution.{u} : type_of% @OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both_oai.{u} := @OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both_oai.{u}
