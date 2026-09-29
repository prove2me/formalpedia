-- Prove2me | solution 1 for NumberField.denseRange_algebraMap_pi_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:18:04.859139+00:00
-- url     : https://prove2.me/submissions/d378eb59-014d-430a-b26b-abbd8a75e0cb

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false

namespace EXTNorm

open Matrix in
theorem det_blockDiagonal'' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (d : ∀ i, Matrix (m i) (m i) R) : (blockDiagonal' d).det = ∏ i, (d i).det := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  let e : m k ≃ {a : Σ i, m i // a.1 = k} :=
    { toFun := fun a => ⟨⟨k, a⟩, rfl⟩
      invFun := fun a => cast (congrArg m a.2) a.1.2
      left_inv := fun a => rfl
      right_inv := by
        rintro ⟨⟨i, a⟩, rfl⟩
        rfl }
  rw [← det_submatrix_equiv_self e]
  congr 1
  ext a b
  simp [e, toSquareBlock_def, toSquareBlockProp_def, toBlock]

theorem det_pi_map {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, Module.End R (M i)) :
    LinearMap.det (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) = ∏ i, LinearMap.det (f i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (M i)
  let B := Pi.basis b
  rw [← LinearMap.det_toMatrix B]
  have : LinearMap.toMatrix B B (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
      Matrix.blockDiagonal' fun i => LinearMap.toMatrix (b i) (b i) (f i) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rw [LinearMap.toMatrix_apply, Matrix.blockDiagonal'_apply]
    simp only [B, Pi.basis_apply, Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval]
    by_cases h : i₁ = j₁
    · subst h
      simp [LinearMap.toMatrix_apply]
    · rw [dif_neg h, Pi.single_eq_of_ne h, map_zero]
      simp
  rw [this, det_blockDiagonal'']
  simp [LinearMap.det_toMatrix]

/-- The norm of a finite product of finite free algebras is the product of the norms. -/
theorem norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (z : ∀ i, A i) :
    Algebra.norm R z = ∏ i, Algebra.norm R (z i) := by
  classical
  rw [Algebra.norm_apply]
  have : Algebra.lmul R (∀ i, A i) z =
      LinearMap.pi fun i => (Algebra.lmul R (A i) (z i)).comp (LinearMap.proj i) := by
    ext x i
    simp
  rw [this, det_pi_map]
  rfl

theorem norm_one_tmul {R : Type*} [Field R] {S : Type*} [Field S] [Algebra R S]
    [FiniteDimensional R S] (A : Type*) [Field A] [Algebra R A] (y : S) :
    Algebra.norm A ((1 : A) ⊗ₜ[R] y) = algebraMap R A (Algebra.norm R y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply TensorProduct.AlgebraTensorModule.ext
  intro a b
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end EXTNorm


namespace EXTNorm

open NumberField IsDedekindDomain WithZero

theorem le_exp_neg_one_of_lt_one {a : ℤᵐ⁰} (ha : a < 1) : a ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact zero_le
  · rw [← exp_log h0] at ha ⊢
    rw [← exp_zero, exp_lt_exp] at ha
    rw [exp_le_exp]
    omega

section Uniformizer

variable {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem valued_coe_int (a : 𝓞 K) :
    Valued.v (algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a)) = w.intValuation a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]

theorem valued_coe (y : K) :
    Valued.v (algebraMap K (w.adicCompletion K) y) = w.valuation K y := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- A uniformizer of the completion, with the norm/valuation dictionary. -/
theorem exists_uniformizer : ∃ ϖ : w.adicCompletion K, Valued.v ϖ = exp (-1 : ℤ) ∧
    ‖ϖ‖ < 1 ∧ ∀ (x : w.adicCompletion K) (n : ℕ), ‖x‖ ≤ ‖ϖ‖ ^ n ↔ Valued.v x ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  refine ⟨algebraMap K _ (algebraMap (𝓞 K) K π), ?_, ?_, ?_⟩
  · rw [valued_coe_int, hπ]
  · rw [Valued.toNormedField.norm_lt_one_iff, valued_coe_int, hπ, ← exp_zero, exp_lt_exp]
    omega
  · intro x n
    rw [← norm_pow, Valued.toNormedField.norm_le_iff, map_pow, valued_coe_int, hπ, ← exp_nsmul]
    simp

theorem mem_closure_range_int {z : w.adicCompletion K} (hz : z ∈ w.adicCompletionIntegers K) :
    z ∈ closure (Set.range fun a : 𝓞 K => algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a)) := by
  obtain ⟨ϖ, -, hϖ1, hϖ⟩ := exists_uniformizer w
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖ1
  have hd := HeightOneSpectrum.denseRange_algebraMap K w
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 (hd.closure_range ▸ Set.mem_univ z :
    z ∈ closure (Set.range (algebraMap K (w.adicCompletion K)))) (min ε 1) (lt_min hε one_pos)
  have hz1 : ‖z‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hz
  have hy1 : ‖algebraMap K (w.adicCompletion K) y‖ ≤ 1 := by
    have h1 : ‖algebraMap K (w.adicCompletion K) y - z‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]; exact lt_of_lt_of_le hy (min_le_right _ _)
    calc ‖algebraMap K (w.adicCompletion K) y‖ = ‖(algebraMap K (w.adicCompletion K) y - z) + z‖ := by
          rw [sub_add_cancel]
      _ ≤ max ‖algebraMap K (w.adicCompletion K) y - z‖ ‖z‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le h1.le hz1
  have hyv : w.valuation K y ≤ 1 := by
    rw [← valued_coe, ← Valued.toNormedField.norm_le_one_iff]; exact hy1
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer w hyv
    (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
  refine ⟨_, ⟨a, rfl⟩, ?_⟩
  have ha' : ‖algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a) -
      algebraMap K (w.adicCompletion K) y‖ < ε := by
    refine lt_of_le_of_lt ?_ hn
    rw [hϖ, ← map_sub, valued_coe]
    exact ha.le
  calc dist z (algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a))
      ≤ max (dist z (algebraMap K (w.adicCompletion K) y))
          (dist (algebraMap K (w.adicCompletion K) y)
            (algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a))) :=
        IsUltrametricDist.dist_triangle_max _ _ _
    _ < ε := by
      refine max_lt (lt_of_lt_of_le hy (min_le_left _ _)) ?_
      rw [dist_comm, dist_eq_norm]; exact ha'

end Uniformizer

section Local

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))

noncomputable instance instNontriviallyNormedFieldAdic :
    NontriviallyNormedField (v.adicCompletion F) :=
  Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰

example : (instNontriviallyNormedFieldAdic v).toNormedField =
    HeightOneSpectrum.instNormedFieldValuedAdicCompletion F v := rfl

variable [Algebra (v.adicCompletion F) (w.adicCompletion K)]
  [ContinuousSMul (v.adicCompletion F) (w.adicCompletion K)]
  [IsScalarTower F (v.adicCompletion F) (w.adicCompletion K)]

theorem continuous_norm_local :
    Continuous (Algebra.norm (v.adicCompletion F) : w.adicCompletion K → v.adicCompletion F) := by
  let b := Module.finBasis (v.adicCompletion F) (w.adicCompletion K)
  have hfun : (Algebra.norm (v.adicCompletion F) : w.adicCompletion K → v.adicCompletion F) =
      fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [hfun]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  exact (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
    (continuous_id.mul continuous_const)

omit [ContinuousSMul (v.adicCompletion F) (w.adicCompletion K)] in
theorem norm_int_mem (a : 𝓞 K) :
    Algebra.norm (v.adicCompletion F) (algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a))
      ∈ v.adicCompletionIntegers F := by
  let : Algebra (v.adicCompletionIntegers F) (w.adicCompletion K) :=
    ((algebraMap (v.adicCompletion F) (w.adicCompletion K)).comp
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  have : IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) (w.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 : IsIntegral (v.adicCompletionIntegers F)
      (algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F))
      (algebraMap K (w.adicCompletion K)) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)
  have h3 := Algebra.isIntegral_norm (v.adicCompletion F) h2
  exact (HeightOneSpectrum.adicCompletionIntegers.integers F v).mem_of_integral h3


theorem norm_mem_of_mem {z : w.adicCompletion K} (hz : z ∈ w.adicCompletionIntegers K) :
    Algebra.norm (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by
  have hS : IsClosed ((Algebra.norm (v.adicCompletion F) : w.adicCompletion K → v.adicCompletion F) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (Valued.isClosed_valuationSubring (v.adicCompletion F)).preimage (continuous_norm_local v w)
  have hsub : (Set.range fun a : 𝓞 K => algebraMap K (w.adicCompletion K) (algebraMap (𝓞 K) K a)) ⊆
      (Algebra.norm (v.adicCompletion F) : w.adicCompletion K → v.adicCompletion F) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro _ ⟨a, rfl⟩
    exact norm_int_mem v w a
  exact hS.closure_subset_iff.2 hsub (mem_closure_range_int w hz)

/-- The local norm restricted to the rings of integers. -/
noncomputable def normInt : w.adicCompletionIntegers K →* v.adicCompletionIntegers F where
  toFun z := ⟨Algebra.norm (v.adicCompletion F) (z : w.adicCompletion K), norm_mem_of_mem v w z.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem coe_normInt (z : w.adicCompletionIntegers K) :
    ((normInt v w z : v.adicCompletionIntegers F) : v.adicCompletion F) =
      Algebra.norm (v.adicCompletion F) (z : w.adicCompletion K) := rfl

theorem continuous_normInt : Continuous (normInt v w) :=
  continuous_induced_rng.2 ((continuous_norm_local v w).comp continuous_subtype_val)

/-- The local norm on unit groups `𝓞_w^× → 𝓞_v^×`. -/
noncomputable def unitNorm : (w.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers F)ˣ :=
  Units.map (normInt v w)

theorem continuous_unitNorm : Continuous (unitNorm v w) := by
  rw [Units.continuous_iff]
  exact ⟨(continuous_normInt v w).comp Units.continuous_val,
    (continuous_normInt v w).comp (Units.continuous_val.comp continuous_inv)⟩

theorem coe_unitNorm (u : (w.adicCompletionIntegers K)ˣ) :
    (((unitNorm v w u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F) = Algebra.norm (v.adicCompletion F) ((u : w.adicCompletionIntegers K) :
        w.adicCompletion K) := rfl

omit [ContinuousSMul (v.adicCompletion F) (w.adicCompletion K)] in
/-- If `‖c‖ < 1` in `F_v` then the image of `c` in `K_w` has valuation at most `exp (-e)`. -/
theorem valued_algebraMap_le [w.asIdeal.LiesOver v.asIdeal]
    (hc : ∀ x : F, algebraMap (v.adicCompletion F) (w.adicCompletion K)
      (algebraMap F (v.adicCompletion F) x) = algebraMap K (w.adicCompletion K) (algebraMap F K x))
    (hcont : Continuous (algebraMap (v.adicCompletion F) (w.adicCompletion K)))
    {c : v.adicCompletion F} (hc1 : ‖c‖ < 1) :
    Valued.v (algebraMap (v.adicCompletion F) (w.adicCompletion K) c) ≤
      exp (-((v.asIdeal.ramificationIdx' w.asIdeal : ℕ) : ℤ)) := by
  obtain ⟨ϖ, -, -, hϖ⟩ := exists_uniformizer w
  set e := v.asIdeal.ramificationIdx' w.asIdeal
  have hS : IsClosed {c : v.adicCompletion F |
      ‖algebraMap (v.adicCompletion F) (w.adicCompletion K) c‖ ≤ ‖ϖ‖ ^ e} :=
    isClosed_le (continuous_norm.comp hcont) continuous_const
  have hT : IsOpen {c : v.adicCompletion F | ‖c‖ < 1} :=
    isOpen_lt continuous_norm continuous_const
  have hsub : {c : v.adicCompletion F | ‖c‖ < 1} ∩ Set.range (algebraMap F (v.adicCompletion F)) ⊆
      {c : v.adicCompletion F |
        ‖algebraMap (v.adicCompletion F) (w.adicCompletion K) c‖ ≤ ‖ϖ‖ ^ e} := by
    rintro _ ⟨hx1, x, rfl⟩
    simp only [Set.mem_setOf_eq] at hx1 ⊢
    rw [hϖ, hc, valued_coe, ← HeightOneSpectrum.valuation_liesOver K v w x]
    rw [Valued.toNormedField.norm_lt_one_iff, valued_coe] at hx1
    have := le_exp_neg_one_of_lt_one hx1
    calc (HeightOneSpectrum.valuation F v x) ^ e ≤ (exp (-1 : ℤ)) ^ e := pow_le_pow_left₀ zero_le this e
      _ = exp (-(e : ℤ)) := by rw [← exp_nsmul]; simp
  have := hS.closure_subset_iff.2 hsub
    ((HeightOneSpectrum.denseRange_algebraMap F v).open_subset_closure_inter hT hc1)
  simpa [hϖ] using this

end Local

end EXTNorm


namespace EXTNorm

open NumberField IsDedekindDomain WithZero

section Family

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
variable (v : HeightOneSpectrum (𝓞 F)) {ι : Type*} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 K))
  [∀ i, Algebra (v.adicCompletion F) ((w i).adicCompletion K)]
  [∀ i, ContinuousSMul (v.adicCompletion F) ((w i).adicCompletion K)]
  [∀ i, IsScalarTower F (v.adicCompletion F) ((w i).adicCompletion K)]

omit [∀ i, ContinuousSMul (v.adicCompletion F) ((w i).adicCompletion K)] in
theorem algebraMap_compat (i : ι) (x : F) :
    algebraMap (v.adicCompletion F) ((w i).adicCompletion K) (algebraMap F (v.adicCompletion F) x) =
      algebraMap K ((w i).adicCompletion K) (algebraMap F K x) := by
  rw [← IsScalarTower.algebraMap_apply F (v.adicCompletion F) ((w i).adicCompletion K),
    IsScalarTower.algebraMap_apply F K ((w i).adicCompletion K)]

omit [∀ i, IsScalarTower F (v.adicCompletion F) ((w i).adicCompletion K)] in
theorem continuous_algebraMap' (i : ι) :
    Continuous (algebraMap (v.adicCompletion F) ((w i).adicCompletion K)) := by
  have : (algebraMap (v.adicCompletion F) ((w i).adicCompletion K) :
      v.adicCompletion F → (w i).adicCompletion K) = fun c => c • (1 : (w i).adicCompletion K) :=
    funext fun c => Algebra.algebraMap_eq_smul_one c
  rw [this]
  exact continuous_id.smul continuous_const

theorem algebraMap_int_compat (a : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (algebraMap (𝓞 F) F a) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

set_option linter.deprecated false in
theorem finrank_le_finrank_pi [∀ i, (w i).asIdeal.LiesOver v.asIdeal]
    (hcover : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.LiesOver v.asIdeal → ∃ i, w i = P) :
    Module.finrank F K ≤ Module.finrank (v.adicCompletion F) (∀ i, (w i).adicCompletion K) := by
  classical
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  have hQ : Module.finrank (𝓞 F ⧸ v.asIdeal) (𝓞 K ⧸ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 K))) =
      Module.finrank F K := Ideal.finrank_quotient_map v.asIdeal F K
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 K ⧸ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 K))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 F) _ _
  let bQ := Module.finBasis (𝓞 F ⧸ v.asIdeal) (𝓞 K ⧸ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 K)))
  choose x hx using fun j => Ideal.Quotient.mk_surjective (bQ j)
  let X : Fin _ → ∀ i, (w i).adicCompletion K :=
    fun j i => algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K (x j))
  have hli : LinearIndependent (v.adicCompletion F) X := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨j0, hj0⟩ := hne
    haveI : Nonempty (Fin (Module.finrank (𝓞 F ⧸ v.asIdeal)
        (𝓞 K ⧸ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 K))))) := ⟨j0⟩
    obtain ⟨j1, hj1⟩ := Finite.exists_max (fun j => ‖g j‖)
    have hg1 : g j1 ≠ 0 := by
      intro h
      have := hj1 j0
      rw [h, norm_zero] at this
      exact hj0 (norm_le_zero_iff.1 this)
    set c := fun j => g j / g j1 with hcdef
    have hc_le : ∀ j, ‖c j‖ ≤ 1 := by
      intro j
      rw [hcdef, norm_div, div_le_one (norm_pos_iff.2 hg1)]
      exact hj1 j
    have hc1 : c j1 = 1 := div_self hg1
    have hcsum : ∑ j, c j • X j = 0 := by
      have : ∑ j, c j • X j = (g j1)⁻¹ • ∑ j, g j • X j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, hcdef]
        simp only [div_eq_inv_mul]
      rw [this, hg, smul_zero]
    have happrox : ∀ j, ∃ a : 𝓞 F,
        ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - c j‖ < 1 := by
      intro j
      have hmem : c j ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
        exact hc_le j
      obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.1 (mem_closure_range_int v hmem) 1 one_pos
      exact ⟨a, by rw [← dist_eq_norm, dist_comm]; exact ha⟩
    choose a ha using happrox
    set s : 𝓞 K := ∑ j, algebraMap (𝓞 F) (𝓞 K) (a j) * x j with hsdef
    have hs_mem : ∀ i, s ∈ (w i).asIdeal ^ (v.asIdeal.ramificationIdx' (w i).asIdeal) := by
      intro i
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← valued_coe_int]
      have h0 : ∑ j, algebraMap (v.adicCompletion F) ((w i).adicCompletion K) (c j) * X j i = 0 := by
        have := congrFun hcsum i
        simpa [Finset.sum_apply, Algebra.smul_def] using this
      have hexpr : algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K s) =
          ∑ j, algebraMap (v.adicCompletion F) ((w i).adicCompletion K)
            (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a j)) - c j) * X j i := by
        simp only [map_sub, sub_mul, Finset.sum_sub_distrib, h0, sub_zero]
        simp only [hsdef, map_sum, map_mul, X, algebraMap_compat, algebraMap_int_compat]
      rw [hexpr]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul]
      have h1 := valued_algebraMap_le v (w i) (algebraMap_compat v w i)
        (continuous_algebraMap' v w i) (ha j)
      have h2 : Valued.v (X j i) ≤ 1 := by
        simp only [X]
        rw [valued_coe_int]
        exact HeightOneSpectrum.intValuation_le_one _ _
      calc _ ≤ exp (-((v.asIdeal.ramificationIdx' (w i).asIdeal : ℕ) : ℤ)) * 1 :=
            mul_le_mul' h1 h2
        _ = _ := mul_one _
    have hne : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
      exact v.ne_bot
    have hsQ : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 K))) s = 0 := by
      apply (Ideal.Factors.piQuotientEquiv v.asIdeal hne).injective
      rw [map_zero, Ideal.Factors.piQuotientEquiv_mk]
      funext P
      rw [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨i, hi⟩ := hcover ⟨P.1, Ideal.Factors.isPrime v.asIdeal P,
        Ideal.Factors.ne_bot v.asIdeal P⟩ (Ideal.Factors.liesOver v.asIdeal P)
      have := hs_mem i
      rw [hi] at this
      exact this
    have hlin : ∑ j, (Ideal.Quotient.mk v.asIdeal (a j)) • bQ j = 0 := by
      rw [← hsQ, hsdef, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hx j, Ideal.Quotient.mk_smul_mk_quotient_map_quotient]
    have hz := (Fintype.linearIndependent_iff.1 bQ.linearIndependent) _ hlin j1
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    have hlt : ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a j1))‖ < 1 := by
      rw [Valued.toNormedField.norm_lt_one_iff, valued_coe_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hz
    have hj1' := ha j1
    rw [hc1] at hj1'
    have h1 : ‖(1 : v.adicCompletion F)‖ < 1 := by
      calc ‖(1 : v.adicCompletion F)‖ =
            ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a j1)) +
              -(algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a j1)) - 1)‖ := by
            rw [neg_sub, add_sub_cancel]
        _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
        _ = max _ _ := by rw [norm_neg]
        _ < 1 := max_lt hlt hj1'
    simp at h1
  have := hli.fintype_card_le_finrank
  simpa [hQ] using this


omit [∀ i, Algebra (v.adicCompletion F) ((w i).adicCompletion K)]
  [∀ i, ContinuousSMul (v.adicCompletion F) ((w i).adicCompletion K)]
  [∀ i, IsScalarTower F (v.adicCompletion F) ((w i).adicCompletion K)] in
/-- Approximation of integral points of `∏ K_w` by global integers (Chinese remainder theorem). -/
theorem mem_closure_diag_int (hw : Function.Injective w) {z : ∀ i, (w i).adicCompletion K}
    (hz : ∀ i, z i ∈ (w i).adicCompletionIntegers K) :
    z ∈ closure (Set.range fun a : 𝓞 K =>
      fun i => algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K a)) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  choose ϖ hϖ using fun i => exists_uniformizer (w i)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ i, ‖ϖ i‖ ^ n < ε := by
    rw [Filter.eventually_all]
    intro i
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hϖ i).2.1).eventually
      (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := hev.exists
  have happrox : ∀ i, ∃ a : 𝓞 K, dist (z i)
      (algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K a)) < ε := by
    intro i
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.1 (mem_closure_range_int (w i) (hz i)) ε hε
    exact ⟨a, ha⟩
  choose a ha using happrox
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun i => (w i).asIdeal) (fun _ => N) (fun i _ => (w i).prime)
    (fun i _ j _ hij h => hij (hw (HeightOneSpectrum.ext h))) (fun i => a i.1)
  refine ⟨_, ⟨t, rfl⟩, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  have hti := ht i (Finset.mem_univ i)
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← valued_coe_int, map_sub, map_sub,
    ← (hϖ i).2.2] at hti
  calc dist (z i) (algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K t))
      ≤ max (dist (z i) (algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K (a i))))
          (dist (algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K (a i)))
            (algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K t))) :=
        IsUltrametricDist.dist_triangle_max _ _ _
    _ < ε := by
      refine max_lt (ha i) ?_
      rw [dist_comm, dist_eq_norm]
      exact lt_of_le_of_lt hti (hN i)

omit [∀ i, Algebra (v.adicCompletion F) ((w i).adicCompletion K)]
  [∀ i, ContinuousSMul (v.adicCompletion F) ((w i).adicCompletion K)]
  [∀ i, IsScalarTower F (v.adicCompletion F) ((w i).adicCompletion K)] in
/-- Weak approximation: `K` is dense in `∏_i K_{w_i}` for distinct primes `w_i`. -/
theorem denseRange_diag (hw : Function.Injective w) :
    DenseRange (fun y : K => fun i => algebraMap K ((w i).adicCompletion K) y) := by
  classical
  intro z
  have hb : ∀ i, ∃ b ∈ nonZeroDivisors (𝓞 K),
      z i * algebraMap (𝓞 K) ((w i).adicCompletion K) b ∈ (w i).adicCompletionIntegers K :=
    fun i => HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (w i) (z i)
  choose b hb0 hbz using hb
  set s : 𝓞 K := ∏ i, b i with hsdef
  have hs0 : s ≠ 0 := by
    rw [hsdef, Finset.prod_ne_zero_iff]
    exact fun i _ => nonZeroDivisors.ne_zero (hb0 i)
  have hcoe : ∀ i (r : 𝓞 K), algebraMap (𝓞 K) ((w i).adicCompletion K) r =
      algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K r) := fun i r =>
    IsScalarTower.algebraMap_apply (𝓞 K) K ((w i).adicCompletion K) r
  have hint : ∀ i (r : 𝓞 K), algebraMap (𝓞 K) ((w i).adicCompletion K) r ∈
      (w i).adicCompletionIntegers K := fun i r => by
    rw [hcoe, HeightOneSpectrum.mem_adicCompletionIntegers, valued_coe_int]
    exact HeightOneSpectrum.intValuation_le_one _ _
  let sz : ∀ i, (w i).adicCompletion K := fun i => z i * algebraMap (𝓞 K) ((w i).adicCompletion K) s
  have hsz : ∀ i, sz i ∈ (w i).adicCompletionIntegers K := by
    intro i
    have : s = b i * ∏ j ∈ Finset.univ.erase i, b j := by
      rw [hsdef, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [sz]
    rw [this, map_mul, ← mul_assoc]
    exact mul_mem (hbz i) (hint i _)
  have h1 := mem_closure_diag_int w hw hsz
  have h2 : closure (Set.range fun a : 𝓞 K =>
      fun i => algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K a)) ⊆
      closure (Set.range fun y : K => fun i => algebraMap K ((w i).adicCompletion K) y) :=
    closure_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  set sinv : K := (algebraMap (𝓞 K) K s)⁻¹
  let m : (∀ i, (w i).adicCompletion K) → (∀ i, (w i).adicCompletion K) :=
    fun u => (fun i => algebraMap K ((w i).adicCompletion K) sinv) * u
  have hm : Continuous m := continuous_const.mul continuous_id
  have hmK : m '' (Set.range fun y : K => fun i => algebraMap K ((w i).adicCompletion K) y) ⊆
      Set.range fun y : K => fun i => algebraMap K ((w i).adicCompletion K) y := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨sinv * y, by funext i; simp [m]⟩
  have hmz : m sz = z := by
    funext i
    have hs0' : algebraMap K ((w i).adicCompletion K) (algebraMap (𝓞 K) K s) ≠ 0 := by
      rw [map_ne_zero, map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
      exact hs0
    simp only [m, sz, Pi.mul_apply, sinv, map_inv₀, hcoe]
    field_simp
  rw [← hmz]
  exact (image_closure_subset_closure_image hm).trans (closure_mono hmK) ⟨sz, h2 h1, rfl⟩

/-- The diagonal `F`-algebra map `K → ∏ K_{w_i}`. -/
noncomputable def diagAlgHom : K →ₐ[F] ∀ i, (w i).adicCompletion K :=
  AlgHom.pi fun i => IsScalarTower.toAlgHom F K ((w i).adicCompletion K)

/-- The canonical map `F_v ⊗_F K → ∏ K_{w_i}`. -/
noncomputable def tensorMap :
    TensorProduct F (v.adicCompletion F) K →ₐ[v.adicCompletion F] ∀ i, (w i).adicCompletion K :=
  Algebra.TensorProduct.lift (Algebra.ofId (v.adicCompletion F) _) (diagAlgHom (F := F) w)
    fun _ _ => Commute.all _ _

theorem tensorMap_one_tmul (y : K) :
    tensorMap v w ((1 : v.adicCompletion F) ⊗ₜ[F] y) =
      fun i => algebraMap K ((w i).adicCompletion K) y := by
  simp only [tensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem tensorMap_surjective (hw : Function.Injective w) : Function.Surjective (tensorMap v w) := by
  have hclosed := Submodule.closed_of_finiteDimensional (LinearMap.range (tensorMap v w).toLinearMap)
  have hsub : Set.range (fun y : K => fun i => algebraMap K ((w i).adicCompletion K) y) ⊆
      (LinearMap.range (tensorMap v w).toLinearMap : Set _) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(1 : v.adicCompletion F) ⊗ₜ[F] y, tensorMap_one_tmul v w y⟩
  intro z
  have := hclosed.closure_subset_iff.2 hsub (denseRange_diag w hw z)
  obtain ⟨t, ht⟩ := this
  exact ⟨t, ht⟩

theorem finrank_pi_le (hw : Function.Injective w) :
    Module.finrank (v.adicCompletion F) (∀ i, (w i).adicCompletion K) ≤ Module.finrank F K := by
  rw [← Module.finrank_baseChange (R := v.adicCompletion F) (S := F) (M' := K)]
  exact LinearMap.finrank_le_finrank_of_surjective (f := (tensorMap v w).toLinearMap)
    (tensorMap_surjective v w hw)


theorem finrank_pi_eq [∀ i, (w i).asIdeal.LiesOver v.asIdeal] (hw : Function.Injective w)
    (hcover : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.LiesOver v.asIdeal → ∃ i, w i = P) :
    Module.finrank (v.adicCompletion F) (∀ i, (w i).adicCompletion K) = Module.finrank F K :=
  le_antisymm (finrank_pi_le v w hw) (finrank_le_finrank_pi v w hcover)

/-- The degree formula `∑_{w | v} [K_w : F_v] = [K : F]`. -/
theorem sum_finrank_eq [∀ i, (w i).asIdeal.LiesOver v.asIdeal] (hw : Function.Injective w)
    (hcover : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.LiesOver v.asIdeal → ∃ i, w i = P) :
    ∑ i, Module.finrank (v.adicCompletion F) ((w i).adicCompletion K) = Module.finrank F K := by
  rw [← Module.finrank_pi_fintype]
  exact finrank_pi_eq v w hw hcover

theorem tensorMap_bijective [∀ i, (w i).asIdeal.LiesOver v.asIdeal] (hw : Function.Injective w)
    (hcover : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.LiesOver v.asIdeal → ∃ i, w i = P) :
    Function.Bijective (tensorMap v w) := by
  refine ⟨?_, tensorMap_surjective v w hw⟩
  have h : Module.finrank (v.adicCompletion F) (TensorProduct F (v.adicCompletion F) K) =
      Module.finrank (v.adicCompletion F) (∀ i, (w i).adicCompletion K) := by
    rw [Module.finrank_baseChange, finrank_pi_eq v w hw hcover]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := (tensorMap v w).toLinearMap)).2 (tensorMap_surjective v w hw)

/-- Local–global compatibility of norms: `N_{K/F}(y) = ∏_{w | v} N_{K_w/F_v}(y)` in `F_v`. -/
theorem algebraMap_norm_eq_prod [∀ i, (w i).asIdeal.LiesOver v.asIdeal] (hw : Function.Injective w)
    (hcover : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.LiesOver v.asIdeal → ∃ i, w i = P) (y : K) :
    algebraMap F (v.adicCompletion F) (Algebra.norm F y) =
      ∏ i, Algebra.norm (v.adicCompletion F) (algebraMap K ((w i).adicCompletion K) y) := by
  rw [← norm_one_tmul (v.adicCompletion F) y,
    ← Algebra.norm_eq_of_algEquiv (AlgEquiv.ofBijective _ (tensorMap_bijective v w hw hcover)),
    AlgEquiv.coe_ofBijective, tensorMap_one_tmul, norm_pi]

end Family

end EXTNorm


namespace EXTNorm

open NumberField IsDedekindDomain

section Main

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem finite_over (v : HeightOneSpectrum (𝓞 F)) :
    Finite {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal} := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := 𝓞 F) (S := 𝓞 K) v.asIdeal
  haveI := hfin.to_subtype
  refine Finite.of_injective (β := v.asIdeal.primesOver (𝓞 K))
    (fun w => ⟨w.1.asIdeal, w.1.isPrime, w.2⟩) ?_
  intro a b h
  exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))

theorem weak_approx (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun w : S => algebraMap K ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K) x) :=
  denseRange_diag (fun w : S => (w : HeightOneSpectrum (𝓞 K))) Subtype.val_injective

variable (v : HeightOneSpectrum (𝓞 F))
  [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
    Algebra (v.adicCompletion F) (w.1.adicCompletion K)]
  [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
    ContinuousSMul (v.adicCompletion F) (w.1.adicCompletion K)]
  [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
    IsScalarTower F (v.adicCompletion F) (w.1.adicCompletion K)]

theorem degree_formula :
    ∑ᶠ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion K) = Module.finrank F K := by
  haveI := finite_over (K := K) v
  letI := Fintype.ofFinite {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}
  haveI : ∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
    w.1.asIdeal.LiesOver v.asIdeal := fun w => w.2
  rw [finsum_eq_sum_of_fintype]
  exact sum_finrank_eq v (fun w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal} => w.1)
    Subtype.val_injective (fun P hP => ⟨⟨P, hP⟩, rfl⟩)

theorem norm_formula (x : K) :
    algebraMap F (v.adicCompletion F) (Algebra.norm F x) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion F) (algebraMap K (w.1.adicCompletion K) x) := by
  haveI := finite_over (K := K) v
  letI := Fintype.ofFinite {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}
  haveI : ∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
    w.1.asIdeal.LiesOver v.asIdeal := fun w => w.2
  rw [finprod_eq_prod_of_fintype]
  exact algebraMap_norm_eq_prod v (fun w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal} => w.1)
    Subtype.val_injective (fun P hP => ⟨⟨P, hP⟩, rfl⟩) x

open scoped TensorProduct in
theorem tensor_equiv :
    ∃ e : v.adicCompletion F ⊗[F] K ≃ₐ[v.adicCompletion F]
        ((w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}) → w.1.adicCompletion K),
      ∀ x : K, e (1 ⊗ₜ x) = fun w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal} =>
        algebraMap K (w.1.adicCompletion K) x := by
  haveI := finite_over (K := K) v
  letI := Fintype.ofFinite {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}
  haveI : ∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
    w.1.asIdeal.LiesOver v.asIdeal := fun w => w.2
  refine ⟨AlgEquiv.ofBijective _ (tensorMap_bijective v
    (fun w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal} => w.1)
    Subtype.val_injective (fun P hP => ⟨⟨P, hP⟩, rfl⟩)), fun x => ?_⟩
  exact tensorMap_one_tmul v _ x

end Main

end EXTNorm


open NumberField IsDedekindDomain
open scoped TensorProduct

theorem solution {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun w : S =>
      algebraMap K ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K) x) :=
  EXTNorm.weak_approx S
