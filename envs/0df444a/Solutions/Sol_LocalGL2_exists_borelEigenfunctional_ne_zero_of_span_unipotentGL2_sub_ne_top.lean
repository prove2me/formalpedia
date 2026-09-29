-- Prove2me | solution 1 for LocalGL2.exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/40b77dca-71b9-5227-9442-1991c688dbc9

import Mathlib
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open IsDedekindDomain NumberField
open FLT.SmoothAdmissibleSchurCommutant
open scoped WithZero

namespace JacquetEmbeddingGL2

theorem exists_eigenfunctional (R : Type*) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ (φ : R →ₐ[ℂ] ℂ) (lam : M →ₗ[ℂ] ℂ), lam ≠ 0 ∧ ∀ (r : R) (m : M), lam (r • m) = φ r * lam m := by
  classical
  obtain ⟨M', hM'co, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  haveI hsimple : IsSimpleModule R (M ⧸ M') := isSimpleModule_iff_isCoatom.mpr hM'co
  obtain ⟨I, hImax, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  haveI : I.IsMaximal := hImax
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  haveI : Module.Finite ℂ (R ⧸ I) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ I)
  haveI : Algebra.IsIntegral ℂ (R ⧸ I) := Algebra.IsIntegral.of_finite ℂ (R ⧸ I)
  have hbij : Function.Bijective (algebraMap ℂ (R ⧸ I)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := R ⧸ I)
  let ε : ℂ ≃+* (R ⧸ I) := RingEquiv.ofBijective (algebraMap ℂ (R ⧸ I)) hbij
  let φ₀ : R →+* ℂ := ε.symm.toRingHom.comp (Ideal.Quotient.mk I)
  have hφ₀ : ∀ c : ℂ, φ₀ (algebraMap ℂ R c) = c := by
    intro c
    show ε.symm (Ideal.Quotient.mk I (algebraMap ℂ R c)) = c
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact ε.symm_apply_apply c
  let φ : R →ₐ[ℂ] ℂ := { φ₀ with commutes' := hφ₀ }
  let lam₀ : M → ℂ := fun m => ε.symm (e (Submodule.Quotient.mk m))
  have hlam_add : ∀ x y : M, lam₀ (x + y) = lam₀ x + lam₀ y := by
    intro x y
    simp only [lam₀, Submodule.Quotient.mk_add, map_add]
  have hlam_smulR : ∀ (r : R) (m : M), lam₀ (r • m) = φ₀ r * lam₀ m := by
    intro r m
    simp only [lam₀, Submodule.Quotient.mk_smul, map_smul]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    rfl
  have hlam_smul : ∀ (c : ℂ) (m : M), lam₀ (c • m) = c * lam₀ m := by
    intro c m
    rw [← algebraMap_smul R c m, hlam_smulR, hφ₀]
  let lam : M →ₗ[ℂ] ℂ := { toFun := lam₀, map_add' := hlam_add, map_smul' := hlam_smul }
  refine ⟨φ, lam, ?_, fun r m => hlam_smulR r m⟩
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective M' (e.symm (ε 1))
  intro h0
  have h1 : lam m = 1 := by
    show ε.symm (e (Submodule.Quotient.mk m)) = 1
    rw [hm, LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
  rw [h0, LinearMap.zero_apply] at h1
  exact zero_ne_one h1

section LocalField

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v

variable (K v) in

def unif : HeightOneSpectrum.adicCompletion K v :=
  ((Classical.choose (v.valuation_exists_uniformizer K) : K) : v.adicCompletion K)

theorem v_unif : Valued.v (unif K v) = WithZero.exp (-1 : ℤ) := by
  rw [unif, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact Classical.choose_spec (v.valuation_exists_uniformizer K)

theorem unif_ne_zero : unif K v ≠ 0 := by
  intro h
  have h1 := v_unif (K := K) (v := v)
  rw [h, Valuation.map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

variable (K v) in

def unifU : (HeightOneSpectrum.adicCompletion K v)ˣ := Units.mk0 (unif K v) unif_ne_zero

theorem v_unifU_zpow (n : ℤ) : Valued.v (((unifU K v ^ n : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)) =
    WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, show ((unifU K v : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = unif K v
    from rfl, map_zpow₀, v_unif, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

theorem exists_eq_unifU_zpow_mul (a : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ∃ (k : ℤ) (u : (HeightOneSpectrum.adicCompletion K v)ˣ), Valued.v (u : F) = 1 ∧ a = unifU K v ^ k * u := by
  have ha : Valued.v (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  set m : ℤ := WithZero.log (Valued.v (a : F)) with hm
  refine ⟨-m, unifU K v ^ m * a, ?_, ?_⟩
  · rw [Units.val_mul, Valuation.map_mul, v_unifU_zpow, ← WithZero.exp_log ha, ← hm, ← WithZero.exp_add,
      neg_add_cancel, WithZero.exp_zero]
  · rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

theorem exists_ball_of_mem_nhds_one {O : Set (HeightOneSpectrum.adicCompletion K v)} (hO : O ∈ nhds (1 : F)) :
    ∃ m : ℤ, m ≤ -1 ∧ ∀ t : F, Valued.v (t - 1) ≤ WithZero.exp m → t ∈ O := by
  obtain ⟨γ, hγ⟩ := (Valued.mem_nhds).mp hO
  set δ : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    intro h0
    have h1 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 *
        MonoidWithZeroHom.ValueGroup₀.embedding (γ⁻¹).1 = (1 : ℤᵐ⁰) := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨min (WithZero.log δ - 1) (-1), min_le_right _ _, fun x hx => ?_⟩
  have hxδ : Valued.v (x - 1) < δ := by
    calc Valued.v (x - 1) ≤ WithZero.exp (min (WithZero.log δ - 1) (-1)) := hx
      _ < WithZero.exp (WithZero.log δ) := WithZero.exp_lt_exp.mpr (by omega)
      _ = δ := WithZero.exp_log hδ0
  have hx' : Valued.v.restrict (x - 1) < γ.1 := by
    rw [Valuation.restrict_lt_iff_lt_embedding]; rw [hδ] at hxδ; exact hxδ
  exact hγ hx'

theorem isCompact_sphere_one : IsCompact {x : HeightOneSpectrum.adicCompletion K v | Valued.v x = 1} := by
  have hcl : IsClosed {x : F | Valued.v x = 1} := by
    convert Valued.isClosed_sphere (R := F) 1 using 1
    ext x
    exact (Valuation.restrict_eq_one_iff _).symm
  refine (NumberField.isCompactAdicCompletionIntegers K v).of_isClosed_subset hcl ?_
  intro x hx
  show x ∈ v.adicCompletionIntegers K
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : HeightOneSpectrum.adicCompletion K v | Valued.v x ≤ WithZero.exp m} := by
  have h0 : Valued.v.restrict (unif K v ^ (-m)) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, map_zpow₀, v_unif]
    exact zpow_ne_zero _ WithZero.exp_ne_zero
  have := Valued.isOpen_closedBall (R := F) h0
  convert this using 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_le_iff, map_zpow₀, v_unif, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]

theorem exists_finset_cover_units (H : Subgroup (HeightOneSpectrum.adicCompletion K v)ˣ) (m : ℤ)
    (hm : ∀ a : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp m → a ∈ H) :
    ∃ S : Finset (HeightOneSpectrum.adicCompletion K v)ˣ,
      ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 → ∃ s ∈ S, s⁻¹ * u ∈ H := by
  let O : (HeightOneSpectrum.adicCompletion K v)ˣ → Set F := fun s =>
    {x : F | Valued.v (((s⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * x - 1) ≤ WithZero.exp m}
  have hO : ∀ s, IsOpen (O s) := by
    intro s
    exact (isOpen_ball m).preimage ((continuous_const.mul continuous_id).sub continuous_const)
  have hcover : {x : F | Valued.v x = 1} ⊆ ⋃ s, O s := by
    intro x hx
    have hx1 : Valued.v x = 1 := hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hx1; exact zero_ne_one hx1
    refine Set.mem_iUnion.mpr ⟨Units.mk0 x hx0, ?_⟩
    show Valued.v ((((Units.mk0 x hx0)⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * x - 1) ≤ WithZero.exp m
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx0, sub_self, Valuation.map_zero]
    exact zero_le'
  obtain ⟨S, hS⟩ := isCompact_sphere_one.elim_finite_subcover O hO hcover
  refine ⟨S, fun u hu => ?_⟩
  have hu' : (u : F) ∈ ⋃ s ∈ S, O s := hS hu
  simp only [Set.mem_iUnion] at hu'
  obtain ⟨s, hs, hsu⟩ := hu'
  refine ⟨s, hs, hm _ ?_⟩
  rwa [Units.val_mul]

theorem exists_ball_of_isOpen_units {H : Subgroup (HeightOneSpectrum.adicCompletion K v)ˣ}
    (hH : IsOpen (H : Set (HeightOneSpectrum.adicCompletion K v)ˣ)) :
    ∃ m : ℤ, m ≤ -1 ∧ ∀ a : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp m → a ∈ H := by
  have h1 : (H : Set (HeightOneSpectrum.adicCompletion K v)ˣ) ∈ nhds (1 : (HeightOneSpectrum.adicCompletion K v)ˣ) :=
    hH.mem_nhds H.one_mem
  rw [(Units.isEmbedding_val₀ (G₀ := F)).isInducing.nhds_eq_comap (1 : (HeightOneSpectrum.adicCompletion K v)ˣ),
    Filter.mem_comap] at h1
  obtain ⟨O, hO, hOH⟩ := h1
  rw [Units.val_one] at hO
  obtain ⟨m, hm, hball⟩ := exists_ball_of_mem_nhds_one hO
  exact ⟨m, hm, fun a ha => hOH (hball _ ha)⟩

theorem exists_finset_zpow_mul_mul {H : Subgroup (HeightOneSpectrum.adicCompletion K v)ˣ}
    (hH : IsOpen (H : Set (HeightOneSpectrum.adicCompletion K v)ˣ)) :
    ∃ S : Finset (HeightOneSpectrum.adicCompletion K v)ˣ, ∀ a : (HeightOneSpectrum.adicCompletion K v)ˣ,
      ∃ (k : ℤ) (s : (HeightOneSpectrum.adicCompletion K v)ˣ) (h : (HeightOneSpectrum.adicCompletion K v)ˣ),
        s ∈ S ∧ h ∈ H ∧ a = unifU K v ^ k * s * h := by
  obtain ⟨m, -, hm⟩ := exists_ball_of_isOpen_units hH
  obtain ⟨S, hS⟩ := exists_finset_cover_units H m hm
  refine ⟨S, fun a => ?_⟩
  obtain ⟨k, u, hu, rfl⟩ := exists_eq_unifU_zpow_mul a
  obtain ⟨s, hs, hsu⟩ := hS u hu
  refine ⟨k, s, s⁻¹ * u, hs, hsu, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]

end LocalField

section GL2

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

abbrev nU (x : HeightOneSpectrum.adicCompletion K v) : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) :=
  AutomorphicForm.unipotentGL2 x

theorem nU_coe (x : F) : ((nU x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : G) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem scalar_coe (a : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) : Mat) = !![(a : F), 0; 0, (a : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem nU_add (x y : F) : (nU (x + y) : G) = nU x * nU y := AutomorphicForm.unipotentGL2_add x y

theorem nU_zero : (nU (0 : F) : G) = 1 := AutomorphicForm.unipotentGL2_zero

theorem diagOne_mul_nU (a : Fˣ) (t : F) :
    (AdelicLevel.diagOne a : G) * nU t = nU ((a : F) * t) * AdelicLevel.diagOne a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, diagOne_coe]

theorem scalar_mul_comm (a : Fˣ) (g : G) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply] <;> ring

theorem borel_eq (g : G) (hg : (g : Mat) 1 0 = 0) (hp : (g : Mat) 0 0 ≠ 0) (hr : (g : Mat) 1 1 ≠ 0) :
    g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((g : Mat) 1 1) hr) *
      AdelicLevel.diagOne (Units.mk0 ((g : Mat) 0 0 / (g : Mat) 1 1) (div_ne_zero hp hr)) *
        nU ((g : Mat) 0 1 / (g : Mat) 0 0) := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, diagOne_coe, hg] <;> field_simp

theorem diag_ne_zero_of_upper (g : G) (hg : (g : Mat) 1 0 = 0) : (g : Mat) 0 0 ≠ 0 ∧ (g : Mat) 1 1 ≠ 0 := by
  have hdet : (g : Mat).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem continuous_diagOne :
    Continuous fun a : (HeightOneSpectrum.adicCompletion K v)ˣ => (AdelicLevel.diagOne a : G) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (fun a : (HeightOneSpectrum.adicCompletion K v)ˣ => ((AdelicLevel.diagOne a : G) : Mat)) =
        fun a : (HeightOneSpectrum.adicCompletion K v)ˣ => !![(a : F), 0; 0, 1] := funext fun a => diagOne_coe a
    rw [show (Units.val ∘ fun a : (HeightOneSpectrum.adicCompletion K v)ˣ => (AdelicLevel.diagOne a : G)) =
      fun a => ((AdelicLevel.diagOne a : G) : Mat) from rfl, this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val
  · have : (fun a : (HeightOneSpectrum.adicCompletion K v)ˣ => (((AdelicLevel.diagOne a : G)⁻¹ : G) : Mat)) =
        fun a => !![((a⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F), 0; 0, 1] := by
      funext a
      rw [← map_inv, diagOne_coe]
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const |
      simpa using (Units.continuous_coe_inv (M := HeightOneSpectrum.adicCompletion K v))

theorem isCompact_integralSubgroup :
    IsCompact ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Subgroup G) : Set G) := by
  haveI : CompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → v.adicCompletionIntegers K))
  haveI : CompactSpace (GL (Fin 2) (v.adicCompletionIntegers K)) := inferInstance
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      continuous_subtype_val.comp ((continuous_apply j).comp (continuous_apply i))
  have hr := isCompact_range hmapcont
  simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range] using hr

end GL2

section Rep

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

variable (π : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) →* Module.End ℂ V)

theorem act_mul (g h : G) (w : V) : π (g * h) w = π g (π h w) := by
  rw [map_mul, Module.End.mul_apply]

def VN : Submodule ℂ V :=
  Submodule.span ℂ {y : V | ∃ (t : HeightOneSpectrum.adicCompletion K v) (z : V),
    y = π (AutomorphicForm.unipotentGL2 t) z - z}

theorem nU_sub_mem (t : F) (z : V) : π (nU t) z - z ∈ VN π :=
  Submodule.subset_span ⟨t, z, rfl⟩

theorem diagOne_mem_VN (a : Fˣ) {y : V} (hy : y ∈ VN π) : π (AdelicLevel.diagOne a) y ∈ VN π := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨t, z, rfl⟩ := hx
      rw [map_sub, ← act_mul, diagOne_mul_nU, act_mul]
      exact nU_sub_mem π _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

def tauLin (a : Fˣ) : (V ⧸ VN π) →ₗ[ℂ] (V ⧸ VN π) :=
  (VN π).mapQ (VN π) (π (AdelicLevel.diagOne a)) fun y hy => diagOne_mem_VN π a hy

theorem tauLin_mk (a : Fˣ) (w : V) :
    tauLin π a (Submodule.Quotient.mk w) = Submodule.Quotient.mk (π (AdelicLevel.diagOne a) w) := rfl

def tau : (HeightOneSpectrum.adicCompletion K v)ˣ →* Module.End ℂ (V ⧸ VN π) where
  toFun := tauLin π
  map_one' := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro w
    show tauLin π 1 (Submodule.Quotient.mk w) = Submodule.Quotient.mk w
    rw [tauLin_mk, map_one, map_one, Module.End.one_apply]
  map_mul' a b := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro w
    show tauLin π (a * b) (Submodule.Quotient.mk w) = tauLin π a (tauLin π b (Submodule.Quotient.mk w))
    rw [tauLin_mk, tauLin_mk, tauLin_mk, map_mul, act_mul]

theorem tau_mk (a : Fˣ) (w : V) :
    tau π a (Submodule.Quotient.mk w) = Submodule.Quotient.mk (π (AdelicLevel.diagOne a) w) := rfl

theorem mk_nU (t : F) (w : V) :
    (Submodule.Quotient.mk (π (nU t) w) : V ⧸ VN π) = Submodule.Quotient.mk w :=
  (Submodule.Quotient.eq _).mpr (nU_sub_mem π t w)

section Centre

variable (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
include hsm hadm hirr

theorem exists_central_scalar (a : Fˣ) :
    ∃ c : ℂ, ∀ x : V, π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) x = c • x := by
  have hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G) :=
    ⟨AdelicDock.localLevelOne (𝓞 K) K v v.asIdeal, AdelicDock.isCompact_and_isOpen_localLevelOne K v v.asIdeal v.ne_bot⟩
  refine exists_forall_eq_smul_of_smooth_admissible π hK₀ hsm hadm hirr fun g => ?_
  rw [← map_mul, ← map_mul, scalar_mul_comm]

end Centre

def omega0 (a : (HeightOneSpectrum.adicCompletion K v)ˣ) : ℂ :=
  by classical exact
    if h : ∃ c : ℂ, ∀ x : V, π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) x = c • x then h.choose else 0

section Centre2

variable {π}
variable (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
include hsm hadm hirr

theorem omega0_spec (a : Fˣ) (x : V) : π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) x = omega0 π a • x := by
  classical
  have h := exists_central_scalar π hsm hadm hirr a
  rw [omega0, dif_pos h]
  exact h.choose_spec x

theorem omega0_one : omega0 π 1 = 1 := by
  obtain ⟨x, hx⟩ := hirr.1
  have h := omega0_spec hsm hadm hirr 1 x
  rw [map_one, map_one, Module.End.one_apply] at h
  by_contra hne
  apply hx
  have h2 : (1 - omega0 π 1) • x = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm hne
  · exact h3

theorem omega0_mul (a b : Fˣ) : omega0 π (a * b) = omega0 π a * omega0 π b := by
  obtain ⟨x, hx⟩ := hirr.1
  have h := omega0_spec hsm hadm hirr (a * b) x
  rw [map_mul, act_mul, omega0_spec hsm hadm hirr b, map_smul, omega0_spec hsm hadm hirr a, smul_smul] at h
  by_contra hne
  apply hx
  have h2 : (omega0 π b * omega0 π a - omega0 π (a * b)) • x = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd ((sub_eq_zero.mp h3).symm.trans (mul_comm _ _)) hne
  · exact h3

def omega : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := omega0 π
      map_one' := omega0_one hsm hadm hirr
      map_mul' := omega0_mul hsm hadm hirr }

theorem omega_apply (a : Fˣ) : ((omega hsm hadm hirr a : ℂˣ) : ℂ) = omega0 π a := rfl

end Centre2

section FiniteGeneration

variable {π}
variable (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)

theorem exists_finset_orbit (hsm : IsSmoothRep π) (v₀ : V) :
    ∃ t : Finset G, ∀ k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      ∃ g ∈ t, π k v₀ = π g v₀ := by
  let S : Subgroup G := repStabilizer π v₀
  have hS : IsOpen (S : Set G) := hsm v₀
  let U : G → Set G := fun g => {x | g⁻¹ * x ∈ S}
  have hU : ∀ g, IsOpen (U g) := fun g => hS.preimage (continuous_const.mul continuous_id)
  have hcover : ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Subgroup G) : Set G)
      ⊆ ⋃ g, U g := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, show x⁻¹ * x ∈ S by rw [inv_mul_cancel]; exact S.one_mem⟩
  obtain ⟨t, ht⟩ := isCompact_integralSubgroup.elim_finite_subcover U hU hcover
  refine ⟨t, fun k hk => ?_⟩
  have hk' : k ∈ ⋃ g ∈ t, U g := ht hk
  simp only [Set.mem_iUnion] at hk'
  obtain ⟨g, hg, hgk⟩ := hk'
  refine ⟨g, hg, ?_⟩
  have h1 : π (g⁻¹ * k) v₀ = v₀ := hgk
  calc π k v₀ = π (g * (g⁻¹ * k)) v₀ := by rw [mul_inv_cancel_left]
    _ = π g v₀ := by rw [act_mul, h1]

include hirr in

theorem span_orbit_eq_top {v₀ : V} (hv₀ : v₀ ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G => π g v₀) = ⊤ := by
  have hstab : ∀ (h : G) (x : V), x ∈ Submodule.span ℂ (Set.range fun g : G => π g v₀) →
      π h x ∈ Submodule.span ℂ (Set.range fun g : G => π g v₀) := by
    intro h x hx
    have hle : Submodule.map (π h) (Submodule.span ℂ (Set.range fun g : G => π g v₀)) ≤
        Submodule.span ℂ (Set.range fun g : G => π g v₀) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨g, rfl⟩
      refine Submodule.subset_span ⟨h * g, ?_⟩
      show π (h * g) v₀ = π h (π g v₀)
      rw [act_mul]
    exact hle ⟨x, hx, rfl⟩
  rcases hirr.2 _ hstab with h | h
  · exfalso
    apply hv₀
    have : v₀ ∈ Submodule.span ℂ (Set.range fun g : G => π g v₀) :=
      Submodule.subset_span ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at this
    exact this
  · exact h

include hsm hadm hirr in

theorem exists_finset_span_tau_eq_top {v₀ : V} (hv₀ : v₀ ≠ 0) :
    ∃ t : Finset G, Submodule.span ℂ {x : V ⧸ VN π | ∃ (a : Fˣ) (g : G), g ∈ t ∧
      x = tau π a (Submodule.Quotient.mk (π g v₀))} = ⊤ := by
  obtain ⟨t, ht⟩ := exists_finset_orbit hsm v₀
  refine ⟨t, ?_⟩
  set W : Submodule ℂ (V ⧸ VN π) := Submodule.span ℂ {x : V ⧸ VN π | ∃ (a : Fˣ) (g : G), g ∈ t ∧
      x = tau π a (Submodule.Quotient.mk (π g v₀))} with hW

  have hmem : ∀ g : G, (Submodule.Quotient.mk (π g v₀) : V ⧸ VN π) ∈ W := by
    intro g
    obtain ⟨b, k, hk, hb10, rfl⟩ :=
      LocalGL2.iwasawa_decomposition (v.adicCompletionIntegers K) (v.adicCompletion K) g
    obtain ⟨g₁, hg₁, hkg₁⟩ := ht k hk
    obtain ⟨hp, hr⟩ := diag_ne_zero_of_upper b hb10
    rw [act_mul, hkg₁, borel_eq b hb10 hp hr, act_mul, act_mul, omega0_spec hsm hadm hirr,
      Submodule.Quotient.mk_smul, ← tau_mk, mk_nU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, g₁, hg₁, rfl⟩)

  rw [eq_top_iff]
  rintro q -
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (VN π) q
  have hw : w ∈ Submodule.span ℂ (Set.range fun g : G => π g v₀) := by
    rw [span_orbit_eq_top hirr hv₀]; exact Submodule.mem_top
  have hle : Submodule.map (VN π).mkQ (Submodule.span ℂ (Set.range fun g : G => π g v₀)) ≤ W := by
    rw [Submodule.map_span_le]
    rintro _ ⟨g, rfl⟩
    exact hmem g
  exact hle ⟨w, hw, rfl⟩

end FiniteGeneration

section Descent

variable {π}

def Hfix (t : Finset (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))) (v₀ : V) :
    Subgroup (HeightOneSpectrum.adicCompletion K v)ˣ :=
  ⨅ g ∈ t, (repStabilizer π (π g v₀)).comap
    (AdelicLevel.diagOne : (HeightOneSpectrum.adicCompletion K v)ˣ →* GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))

theorem mem_Hfix {t : Finset G} {v₀ : V} {a : Fˣ} :
    a ∈ Hfix (π := π) t v₀ ↔ ∀ g ∈ t, π (AdelicLevel.diagOne a) (π g v₀) = π g v₀ := by
  simp only [Hfix, Subgroup.mem_iInf, Subgroup.mem_comap, mem_repStabilizer]

theorem isOpen_Hfix (hsm : IsSmoothRep π) (t : Finset G) (v₀ : V) :
    IsOpen ((Hfix (π := π) t v₀ : Subgroup Fˣ) : Set Fˣ) := by
  have : ((Hfix (π := π) t v₀ : Subgroup Fˣ) : Set Fˣ) =
      ⋂ g ∈ t, (fun a : Fˣ => (AdelicLevel.diagOne a : G)) ⁻¹' (repStabilizer π (π g v₀) : Set G) := by
    ext a
    simp only [SetLike.mem_coe, mem_Hfix, Set.mem_iInter, Set.mem_preimage, mem_repStabilizer]
  rw [this]
  exact isOpen_biInter_finset fun g _ => (hsm (π g v₀)).preimage continuous_diagOne

theorem tau_eq_one_of_mem_Hfix {t : Finset G} {v₀ : V}
    (htop : Submodule.span ℂ {x : V ⧸ VN π | ∃ (a : Fˣ) (g : G), g ∈ t ∧
      x = tau π a (Submodule.Quotient.mk (π g v₀))} = ⊤)
    {h : Fˣ} (hh : h ∈ Hfix (π := π) t v₀) : tau π h = 1 := by
  refine LinearMap.ext_on htop ?_
  rintro _ ⟨a, g, hg, rfl⟩
  rw [Module.End.one_apply, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
    tau_mk π h, (mem_Hfix.mp hh) g hg]

end Descent

section Main

variable {π}
variable (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
include hsm hadm hirr

theorem main (hN : VN π ≠ ⊤) :
    ∃ (χ ω : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ), ℓ ≠ 0 ∧
      (∀ (x : F) (w : V), ℓ (π (AutomorphicForm.unipotentGL2 x) w) = ℓ w) ∧
      (∀ (a : Fˣ) (w : V), ℓ (π (AdelicLevel.diagOne a) w) = χ a * ℓ w) ∧
      (∀ (a : Fˣ) (w : V), ℓ (π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) w) = ω a * ℓ w) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hirr.1
  obtain ⟨t, htop⟩ := exists_finset_span_tau_eq_top hsm hadm hirr hv₀

  set H : Subgroup Fˣ := Hfix (π := π) t v₀ with hHdef
  have hHopen : IsOpen (H : Set Fˣ) := isOpen_Hfix hsm t v₀
  have hHker : H ≤ (tau π).ker := fun h hh => (MonoidHom.mem_ker).mpr (tau_eq_one_of_mem_Hfix htop hh)
  let τbar : Fˣ ⧸ H →* Module.End ℂ (V ⧸ VN π) := QuotientGroup.lift H (tau π) hHker
  have hτbar : ∀ a : Fˣ, τbar (QuotientGroup.mk a) = tau π a := fun a => QuotientGroup.lift_mk H hHker a

  haveI hfg : Group.FG (Fˣ ⧸ H) := by
    obtain ⟨S, hS⟩ := exists_finset_zpow_mul_mul hHopen
    rw [Group.fg_iff]
    refine ⟨insert (QuotientGroup.mk (unifU K v)) (((↑) : Fˣ → Fˣ ⧸ H) '' (S : Set Fˣ)), ?_,
      (Set.Finite.image _ S.finite_toSet).insert _⟩
    rw [eq_top_iff]
    rintro γ -
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
    obtain ⟨k, s, h, hs, hh, rfl⟩ := hS a
    have hh1 : (QuotientGroup.mk h : Fˣ ⧸ H) = 1 := (QuotientGroup.eq_one_iff h).mpr hh
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) k)
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩))) ?_
    rw [hh1]
    exact Subgroup.one_mem _

  let Φ : MonoidAlgebra ℂ (Fˣ ⧸ H) →ₐ[ℂ] Module.End ℂ (V ⧸ VN π) :=
    MonoidAlgebra.lift ℂ (Module.End ℂ (V ⧸ VN π)) (Fˣ ⧸ H) τbar
  letI instMod : Module (MonoidAlgebra ℂ (Fˣ ⧸ H)) (V ⧸ VN π) := Module.compHom (V ⧸ VN π) Φ.toRingHom
  letI instSMul : SMul (MonoidAlgebra ℂ (Fˣ ⧸ H)) (V ⧸ VN π) := instMod.toSMul
  have hsmul_def : ∀ (r : MonoidAlgebra ℂ (Fˣ ⧸ H)) (q : V ⧸ VN π), r • q = Φ r q := fun r q => rfl
  have hof_smul : ∀ (a : Fˣ) (q : V ⧸ VN π),
      (MonoidAlgebra.of ℂ (Fˣ ⧸ H) (QuotientGroup.mk a) : MonoidAlgebra ℂ (Fˣ ⧸ H)) • q = tau π a q := by
    intro a q
    rw [hsmul_def]
    show (MonoidAlgebra.lift ℂ (Module.End ℂ (V ⧸ VN π)) (Fˣ ⧸ H) τbar (MonoidAlgebra.of ℂ (Fˣ ⧸ H) _)) q = _
    rw [MonoidAlgebra.lift_of, hτbar]
  haveI : IsScalarTower ℂ (MonoidAlgebra ℂ (Fˣ ⧸ H)) (V ⧸ VN π) :=
    ⟨fun c r q => by rw [hsmul_def, hsmul_def, map_smul, LinearMap.smul_apply]⟩
  haveI : Module.Finite (MonoidAlgebra ℂ (Fˣ ⧸ H)) (V ⧸ VN π) := by
    refine ⟨⟨t.image fun g => Submodule.Quotient.mk (π g v₀), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    have hq : q ∈ Submodule.span ℂ {x : V ⧸ VN π | ∃ (a : Fˣ) (g : G), g ∈ t ∧
        x = tau π a (Submodule.Quotient.mk (π g v₀))} := by rw [htop]; exact Submodule.mem_top
    have hgens : {x : V ⧸ VN π | ∃ (a : Fˣ) (g : G), g ∈ t ∧ x = tau π a (Submodule.Quotient.mk (π g v₀))} ⊆
        ((Submodule.span (MonoidAlgebra ℂ (Fˣ ⧸ H))
          ((t.image fun g => Submodule.Quotient.mk (π g v₀) : Finset (V ⧸ VN π)) : Set (V ⧸ VN π))).restrictScalars ℂ
            : Set (V ⧸ VN π)) := by
      rintro _ ⟨a, g, hg, rfl⟩
      rw [← hof_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨g, hg, rfl⟩
    exact Submodule.span_le.mpr hgens hq
  haveI : Nontrivial (V ⧸ VN π) := Submodule.Quotient.nontrivial_iff.mpr hN
  haveI : Algebra.FiniteType ℂ (MonoidAlgebra ℂ (Fˣ ⧸ H)) := MonoidAlgebra.finiteType_of_fg

  obtain ⟨φ, lam, hlam0, hlam⟩ := exists_eigenfunctional (MonoidAlgebra ℂ (Fˣ ⧸ H)) (V ⧸ VN π)
  let χ₀ : Fˣ →* ℂ :=
    φ.toRingHom.toMonoidHom.comp ((MonoidAlgebra.of ℂ (Fˣ ⧸ H)).comp (QuotientGroup.mk' H))
  have hχ₀ : ∀ a : Fˣ, χ₀ a = φ (MonoidAlgebra.of ℂ (Fˣ ⧸ H) (QuotientGroup.mk a)) := fun a => rfl
  refine ⟨χ₀.toHomUnits, omega hsm hadm hirr, lam.comp (VN π).mkQ, ?_, ?_, ?_, ?_⟩
  ·
    intro h0
    apply hlam0
    apply LinearMap.ext
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (VN π) q
    have := congrArg (fun f : V →ₗ[ℂ] ℂ => f w) h0
    simpa using this
  ·
    intro x w
    show lam (Submodule.Quotient.mk (π (nU x) w)) = lam (Submodule.Quotient.mk w)
    rw [mk_nU]
  ·
    intro a w
    show lam (Submodule.Quotient.mk (π (AdelicLevel.diagOne a) w)) = _ * lam (Submodule.Quotient.mk w)
    rw [← tau_mk, ← hof_smul, hlam, MonoidHom.coe_toHomUnits, hχ₀]
  ·
    intro a w
    show lam (Submodule.Quotient.mk (π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) w)) =
      _ * lam (Submodule.Quotient.mk w)
    rw [omega0_spec hsm hadm hirr, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul, omega_apply]

end Main

end Rep

end JacquetEmbeddingGL2

end

open IsDedekindDomain NumberField FLT.SmoothAdmissibleSchurCommutant in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : GL (Fin 2) (v.adicCompletion K) →* Module.End ℂ V)
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
    (hN : Submodule.span ℂ {y : V | ∃ (t : v.adicCompletion K) (z : V),
      y = π (AutomorphicForm.unipotentGL2 t) z - z} ≠ ⊤) :
    ∃ (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ), ℓ ≠ 0 ∧
      (∀ (x : v.adicCompletion K) (w : V), ℓ (π (AutomorphicForm.unipotentGL2 x) w) = ℓ w) ∧
      (∀ (a : (v.adicCompletion K)ˣ) (w : V), ℓ (π (AdelicLevel.diagOne a) w) = χ a * ℓ w) ∧
      (∀ (a : (v.adicCompletion K)ˣ) (w : V),
        ℓ (π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) w) = ω a * ℓ w) :=
  JacquetEmbeddingGL2.main hsm hadm hirr hN

end S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
end P2MW
export P2MW.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top (solution)
