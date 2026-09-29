-- Prove2me | solution 1 for NumberField.index_range_norm_dvd_two_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fafd7022-68c1-5ae9-88de-4fa886ccf8e4

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_index_range_norm_dvd_two_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise

namespace QuadNormIndex

section generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (F : Type*) [Field F] [Algebra K F]

theorem smul_tmul_right (s : F) (l : L) (t : F) : s • (l ⊗ₜ[K] t) = l ⊗ₜ[K] (s * t) := by
  rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, TensorProduct.comm_symm_tmul]

theorem algebraMap_right_apply (s : F) : algebraMap F (L ⊗[K] F) s = 1 ⊗ₜ[K] s := rfl

theorem tmul_one_eq_smul_one (l : L) (s : F) : l ⊗ₜ[K] s = s • (l ⊗ₜ[K] (1 : F)) := by
  rw [smul_tmul_right, mul_one]

theorem smul_tmul_one (k : K) (l : L) :
    (k • l) ⊗ₜ[K] (1 : F) = (algebraMap K F k) • (l ⊗ₜ[K] (1 : F)) := by
  rw [smul_tmul_right, mul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

private theorem _root_.QuadNormIndex.basis_apply {ι : Type*} (b : Module.Basis ι K L) (i : ι) :
    TensorProduct.RightActions.Algebra.TensorProduct.basis F b i = b i ⊗ₜ[K] (1 : F) := by
  rw [TensorProduct.RightActions.Algebra.TensorProduct.basis, Module.Basis.map_apply,
    Algebra.TensorProduct.basis_apply]
  rfl

p2m_export "QuadNormIndex" "basis_apply"
end generic

section quad

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def qa (pb : PowerBasis K L) : K := (minpoly K pb.gen).coeff 1
noncomputable def qb (pb : PowerBasis K L) : K := (minpoly K pb.gen).coeff 0

theorem gen_sq (pb : PowerBasis K L) (hdim : pb.dim = 2) :
    pb.gen ^ 2 = -(qa pb • pb.gen) - algebraMap K L (qb pb) := by
  have h0 : Polynomial.aeval pb.gen (minpoly K pb.gen) = 0 := minpoly.aeval K pb.gen
  have hdeg : (minpoly K pb.gen).natDegree = 2 := by rw [pb.natDegree_minpoly, hdim]
  have hmonic : (minpoly K pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hlead : (minpoly K pb.gen).coeff 2 = 1 := by
    have := hmonic.coeff_natDegree; rwa [hdeg] at this
  rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, hlead,
    one_smul] at h0

  rw [Algebra.smul_def, mul_one] at h0
  simp only [qa, qb]
  linear_combination h0

def Q {R : Type*} [CommRing R] (a b x y : R) : R := x ^ 2 - a * x * y + b * y ^ 2

variable (F : Type*) [Field F] [Algebra K F]

noncomputable def Theta (pb : PowerBasis K L) : L ⊗[K] F := pb.gen ⊗ₜ[K] (1 : F)

theorem Theta_sq (pb : PowerBasis K L) (hdim : pb.dim = 2) :
    Theta F pb * Theta F pb =
      -(algebraMap F (L ⊗[K] F) (algebraMap K F (qa pb)) * Theta F pb) -
        algebraMap F (L ⊗[K] F) (algebraMap K F (qb pb)) := by
  simp only [Theta]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← pow_two, gen_sq pb hdim, TensorProduct.sub_tmul,
    TensorProduct.neg_tmul, smul_tmul_one, Algebra.algebraMap_eq_smul_one (qb pb), smul_tmul_one,
    Algebra.smul_def, Algebra.smul_def, ← Algebra.TensorProduct.one_def, mul_one]

noncomputable def basisTwo (pb : PowerBasis K L) (hdim : pb.dim = 2) :
    Module.Basis (Fin 2) F (L ⊗[K] F) :=
  (TensorProduct.RightActions.Algebra.TensorProduct.basis F pb.basis).reindex (finCongr hdim)

theorem basisTwo_apply (pb : PowerBasis K L) (hdim : pb.dim = 2) (j : Fin 2) :
    basisTwo F pb hdim j = (pb.gen ^ (j : ℕ)) ⊗ₜ[K] (1 : F) := by
  rw [basisTwo, Module.Basis.reindex_apply, basis_apply, pb.basis_eq_pow]
  rfl

theorem basisTwo_zero (pb : PowerBasis K L) (hdim : pb.dim = 2) : basisTwo F pb hdim 0 = 1 := by
  rw [basisTwo_apply, Fin.val_zero, pow_zero, ← Algebra.TensorProduct.one_def]

theorem basisTwo_one (pb : PowerBasis K L) (hdim : pb.dim = 2) : basisTwo F pb hdim 1 = Theta F pb := by
  rw [basisTwo_apply, Theta]
  simp

theorem eq_coord (pb : PowerBasis K L) (hdim : pb.dim = 2) (z : L ⊗[K] F) :
    z = algebraMap F (L ⊗[K] F) ((basisTwo F pb hdim).repr z 0) +
        algebraMap F (L ⊗[K] F) ((basisTwo F pb hdim).repr z 1) * Theta F pb := by
  conv_lhs => rw [← (basisTwo F pb hdim).sum_repr z]
  rw [Fin.sum_univ_two, basisTwo_zero, basisTwo_one, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem repr_comb (pb : PowerBasis K L) (hdim : pb.dim = 2) (x y : F) (i : Fin 2) :
    (basisTwo F pb hdim).repr (algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb) i =
      ![x, y] i := by
  have : algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb =
      x • basisTwo F pb hdim 0 + y • basisTwo F pb hdim 1 := by
    rw [basisTwo_zero, basisTwo_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [this, map_add, map_smul, map_smul, (basisTwo F pb hdim).repr_self, (basisTwo F pb hdim).repr_self]
  fin_cases i <;> simp

theorem norm_comb (pb : PowerBasis K L) (hdim : pb.dim = 2) (x y : F) :
    Algebra.norm F (algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb) =
      Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y := by
  classical
  set aF := algebraMap K F (qa pb)
  set bF := algebraMap K F (qb pb)
  have hz1 : (algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb) * basisTwo F pb hdim 1 =
      algebraMap F (L ⊗[K] F) (-(bF * y)) + algebraMap F (L ⊗[K] F) (x - aF * y) * Theta F pb := by
    rw [basisTwo_one]
    simp only [add_mul, mul_assoc, Theta_sq F pb hdim, map_neg, map_mul, map_sub]
    ring
  rw [Algebra.norm_eq_matrix_det (basisTwo F pb hdim), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basisTwo_zero, mul_one, hz1, repr_comb]
  simp only [Q, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem mul_conj (pb : PowerBasis K L) (hdim : pb.dim = 2) (x y : F) :
    (algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb) *
      (algebraMap F (L ⊗[K] F) (x - algebraMap K F (qa pb) * y) - algebraMap F (L ⊗[K] F) y * Theta F pb) =
      algebraMap F (L ⊗[K] F) (Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y) := by
  have hT := Theta_sq F pb hdim
  simp only [Q, map_sub, map_add, map_mul, map_pow]
  linear_combination (-(algebraMap F (L ⊗[K] F) y) ^ 2) * hT

theorem disc_ne_zero (pb : PowerBasis K L) (hdim : pb.dim = 2) (h2 : (2 : K) ≠ 0) :
    qa pb ^ 2 - 4 * qb pb ≠ 0 := by
  intro h
  set c : K := qa pb / 2 with hc
  have hsq := gen_sq pb hdim
  rw [Algebra.smul_def] at hsq
  have ha : algebraMap K L (qa pb) = 2 * algebraMap K L c := by
    rw [hc, map_div₀, map_ofNat, mul_div_cancel₀]
    have := (map_ne_zero (algebraMap K L)).2 h2
    rwa [map_ofNat] at this
  have hb : algebraMap K L (qb pb) = algebraMap K L c ^ 2 := by
    rw [← map_pow]; congr 1
    rw [hc, div_pow]
    field_simp
    linear_combination (-1 : K) * h
  have key : (pb.gen + algebraMap K L c) ^ 2 = 0 := by
    linear_combination hsq - pb.gen * ha - hb
  have hgen : pb.gen = algebraMap K L (-c) := by
    rw [map_neg, eq_neg_iff_add_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 key
  have h1 : (minpoly K pb.gen).natDegree = 1 := by
    rw [hgen, minpoly.eq_X_sub_C L (-c), Polynomial.natDegree_X_sub_C]
  rw [pb.natDegree_minpoly, hdim] at h1
  exact absurd h1 (by norm_num)

theorem discF_ne_zero (pb : PowerBasis K L) (hdim : pb.dim = 2) (h2 : (2 : K) ≠ 0) :
    algebraMap K F (qa pb) ^ 2 - 4 * algebraMap K F (qb pb) ≠ 0 := by
  have := disc_ne_zero pb hdim h2
  rw [← map_pow, ← map_ofNat (algebraMap K F) 4, ← map_mul, ← map_sub]
  exact (map_ne_zero (algebraMap K F)).2 this

noncomputable def unitOf (pb : PowerBasis K L) (hdim : pb.dim = 2) (x y : F)
    (hQ : Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y ≠ 0) : (L ⊗[K] F)ˣ :=
  Units.mkOfMulEqOne (algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb)
    (algebraMap F (L ⊗[K] F) (Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y)⁻¹ *
      (algebraMap F (L ⊗[K] F) (x - algebraMap K F (qa pb) * y) - algebraMap F (L ⊗[K] F) y * Theta F pb))
    (by rw [mul_left_comm, mul_conj F pb hdim, ← map_mul, inv_mul_cancel₀ hQ, map_one])

theorem coe_unitOf (pb : PowerBasis K L) (hdim : pb.dim = 2) (x y : F)
    (hQ : Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y ≠ 0) :
    (unitOf F pb hdim x y hQ : L ⊗[K] F) =
      algebraMap F (L ⊗[K] F) x + algebraMap F (L ⊗[K] F) y * Theta F pb := rfl

theorem norm_unitOf (pb : PowerBasis K L) (hdim : pb.dim = 2) (x y : F)
    (hQ : Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y ≠ 0) :
    (Units.map (Algebra.norm F : L ⊗[K] F →* F) (unitOf F pb hdim x y hQ) : F) =
      Q (algebraMap K F (qa pb)) (algebraMap K F (qb pb)) x y := by
  rw [Units.coe_map, coe_unitOf]
  exact norm_comb F pb hdim x y

theorem range_norm_eq_top_of_root (pb : PowerBasis K L) (hdim : pb.dim = 2) (h2 : (2 : K) ≠ 0)
    (r : F) (hr : r ^ 2 + algebraMap K F (qa pb) * r + algebraMap K F (qb pb) = 0) :
    (Units.map (Algebra.norm F : L ⊗[K] F →* F)).range = ⊤ := by
  set aF := algebraMap K F (qa pb)
  set bF := algebraMap K F (qb pb)
  set r₂ : F := -aF - r with hr₂
  have hne : r - r₂ ≠ 0 := by
    intro h0
    apply discF_ne_zero F pb hdim h2
    have : (r - r₂) ^ 2 = aF ^ 2 - 4 * bF := by
      rw [hr₂]; linear_combination (4 : F) * hr
    rw [← this, h0]; ring
  rw [eq_top_iff]
  rintro t -
  set y : F := ((t : F) - 1) / (r - r₂) with hy
  set x : F := (t : F) - r * y with hx
  have hfac : Q aF bF x y = (x + r * y) * (x + r₂ * y) := by
    simp only [Q, hr₂]; linear_combination (y ^ 2) * hr
  have h1 : x + r * y = t := by rw [hx]; ring
  have h2' : x + r₂ * y = 1 := by
    rw [hx]
    have : (r - r₂) * y = (t : F) - 1 := by rw [hy]; field_simp
    linear_combination (-1 : F) * this
  have hQ : Q aF bF x y = t := by rw [hfac, h1, h2', mul_one]
  have hQ0 : Q aF bF x y ≠ 0 := by rw [hQ]; exact t.ne_zero
  refine ⟨unitOf F pb hdim x y hQ0, Units.ext ?_⟩
  rw [norm_unitOf, hQ]

theorem isUnit_of_no_root (pb : PowerBasis K L) (hdim : pb.dim = 2)
    (hnr : ∀ r : F, r ^ 2 + algebraMap K F (qa pb) * r + algebraMap K F (qb pb) ≠ 0)
    (z : L ⊗[K] F) (hz : z ≠ 0) : IsUnit z := by
  set aF := algebraMap K F (qa pb)
  set bF := algebraMap K F (qb pb)
  set x := (basisTwo F pb hdim).repr z 0
  set y := (basisTwo F pb hdim).repr z 1
  have hzc := eq_coord F pb hdim z
  have hQ : Q aF bF x y ≠ 0 := by
    by_cases hy : y = 0
    · have hx : x ≠ 0 := by
        intro hx
        apply hz
        rw [hzc]
        change algebraMap F _ x + algebraMap F _ y * _ = 0
        rw [hx, hy, map_zero, zero_mul, add_zero]
      simp only [Q, hy, mul_zero, zero_pow two_ne_zero, sub_zero, add_zero]
      exact pow_ne_zero 2 hx
    · have : Q aF bF x y = y ^ 2 * ((-x / y) ^ 2 + aF * (-x / y) + bF) := by
        simp only [Q]; field_simp; ring
      rw [this]
      exact mul_ne_zero (pow_ne_zero 2 hy) (hnr _)
  have : z = unitOf F pb hdim x y hQ := by rw [coe_unitOf]; exact hzc
  rw [this]
  exact Units.isUnit _

end quad

section squares

theorem sq_range_le_norm_range (F E : Type*) [Field F] [CommRing E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    (powMonoidHom 2 : Fˣ →* Fˣ).range ≤ (Units.map (Algebra.norm F : E →* F)).range := by
  rintro _ ⟨s, rfl⟩
  refine ⟨Units.map (algebraMap F E : F →* E) s, Units.ext ?_⟩
  simp only [Units.coe_map, MonoidHom.coe_coe, powMonoidHom_apply, Units.val_pow_eq_pow_val]
  rw [Algebra.norm_algebraMap, h]

theorem mem_sq_range_iff {F : Type*} [Field F] (b : Fˣ) :
    b ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range ↔ ∃ s : F, s ^ 2 = b := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by simp [Units.val_pow_eq_pow_val]⟩
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact b.ne_zero (by rw [← hs]; ring)
    exact ⟨Units.mk0 s hs0, Units.ext (by simp [Units.val_pow_eq_pow_val, hs])⟩

theorem sq_range_index_real (F : Type*) [Field F] (e : F ≃+* ℝ) :
    (powMonoidHom 2 : Fˣ →* Fˣ).range.index = 2 := by
  have hmem : ∀ b : Fˣ, b ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range ↔ 0 < e b := by
    intro b
    rw [mem_sq_range_iff]
    constructor
    · rintro ⟨s, hs⟩
      have hs0 : e s ≠ 0 := by
        rw [map_ne_zero]
        rintro rfl
        exact b.ne_zero (by rw [← hs]; ring)
      rw [← hs, map_pow]
      positivity
    · intro hb
      refine ⟨e.symm (Real.sqrt (e b)), e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, Real.sq_sqrt hb.le]
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b => ?_⟩
  rw [hmem, hmem, Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one, map_neg]
  have hb : e b ≠ 0 := by rw [map_ne_zero]; exact b.ne_zero
  rcases lt_or_gt_of_ne hb with h | h
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨h, by linarith⟩

theorem sq_range_eq_top_complex (F : Type*) [Field F] (e : F ≃+* ℂ) :
    (powMonoidHom 2 : Fˣ →* Fˣ).range = ⊤ := by
  rw [eq_top_iff]
  rintro b -
  rw [mem_sq_range_iff]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e b) two_pos
  exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩

end squares

section localfield

theorem exists_extension (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Nonempty (v.Extension (𝓞 L)) := by
  have hv : v.asIdeal.IsMaximal := v.isMaximal
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
    (FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 L) K L).algebraMap_injective
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hQbot : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ, Ideal.comap_bot_of_injective _ hinj]
  exact ⟨⟨⟨Q, hQmax.isPrime, hQbot⟩, HeightOneSpectrum.ext hQ⟩⟩

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

noncomputable def phi : L ⊗[K] v.adicCompletion K →ₐ[v.adicCompletion K] w.1.adicCompletion L :=
  (Pi.evalAlgHom (v.adicCompletion K) (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v)

theorem finrank_le (h2 : Module.finrank K L = 2) :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤ 2 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have hpi := HeightOneSpectrum.adicCompletion.finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion
    K L (𝓞 L) v
  rw [TensorProduct.finrank_rightAlgebra, h2, Module.finrank_pi_fintype] at hpi
  calc Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)
      ≤ ∑ w' : v.Extension (𝓞 L), Module.finrank (v.adicCompletion K) (w'.1.adicCompletion L) :=
        Finset.single_le_sum (f := fun w' : v.Extension (𝓞 L) => Module.finrank (v.adicCompletion K) (w'.1.adicCompletion L))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    _ = 2 := hpi.symm

open scoped Valued in
theorem continuous_algEquiv (h2 : Module.finrank K L = 2)
    (σ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) : Continuous σ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  exact LinearMap.continuous_of_finiteDimensional (σ.toLinearEquiv.toLinearMap)

open scoped Valued in

theorem norm_lt_one_of_norm_lt_one (h2 : Module.finrank K L = 2)
    (σ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x : w.1.adicCompletion L) (hx : ‖x‖ < 1) : ‖σ x‖ < 1 := by
  have hc := continuous_algEquiv K L v w h2 σ
  have h1 : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
  have h2' : Filter.Tendsto (fun n : ℕ => σ x ^ n) Filter.atTop (nhds 0) := by
    have := (hc.tendsto 0).comp h1
    rw [map_zero] at this
    refine this.congr fun n => ?_
    simp [Function.comp]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 h2'

open scoped Valued in

private theorem _root_.QuadNormIndex.norm_le_one_iff (h2 : Module.finrank K L = 2)
    (σ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x : w.1.adicCompletion L) : ‖σ x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  suffices key : ∀ (τ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (y : w.1.adicCompletion L), ‖y‖ ≤ 1 → ‖τ y‖ ≤ 1 by
    refine ⟨fun h => ?_, key σ x⟩
    have := key σ.symm (σ x) h
    rwa [σ.symm_apply_apply] at this
  intro τ y hy
  by_contra h
  rw [not_le] at h
  have hy0 : τ y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact absurd h (by norm_num)
  have hinv : ‖(τ y)⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have := norm_lt_one_of_norm_lt_one K L v w h2 τ.symm _ hinv
  rw [map_inv₀, τ.symm_apply_apply, norm_inv] at this
  have hy0' : y ≠ 0 := by intro h0; apply hy0; rw [h0, map_zero]
  have : 1 < ‖y‖ := by
    rwa [inv_lt_one₀ (norm_pos_iff.2 hy0')] at this
  exact absurd hy (not_le.2 this)

p2m_export "QuadNormIndex" "norm_le_one_iff"
open scoped Valued in
theorem mem_integers_iff (x : w.1.adicCompletion L) :
    x ∈ w.1.adicCompletionIntegers L ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem decompositionSubgroup_eq_top (h2 : Module.finrank K L = 2) :
    (w.1.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K) = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [AlgEquiv.smul_def, mem_integers_iff, norm_le_one_iff K L v w h2]
    rwa [← mem_integers_iff]
  · intro hx
    refine ⟨σ.symm x, ?_, by rw [AlgEquiv.smul_def, σ.apply_symm_apply]⟩
    rw [mem_integers_iff, show σ.symm = σ⁻¹ from rfl]
    rw [norm_le_one_iff K L v w h2, ← mem_integers_iff]
    exact hx

theorem charZero_adicCompletion : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

theorem range_norm_eq_of_algEquiv {F A B : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing B]
    [Algebra F B] (e : A ≃ₐ[F] B) :
    (Units.map (Algebra.norm F : A →* F)).range = (Units.map (Algebra.norm F : B →* F)).range := by
  have hcomp : (Units.map (Algebra.norm F : A →* F)) =
      (Units.map (Algebra.norm F : B →* F)).comp (Units.map (e : A →* B)) := by
    ext z
    simp [Algebra.norm_eq_of_algEquiv]
  have hsurj : (Units.map (e : A →* B)).range = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    refine ⟨Units.map (e.symm : B →* A) t, Units.ext ?_⟩
    simp
  rw [hcomp, MonoidHom.range_comp, hsurj, ← MonoidHom.range_eq_map]

theorem index_range_norm_local (h2 : Module.finrank K L = 2)
    [hq : Algebra.IsQuadraticExtension (v.adicCompletion K) (w.1.adicCompletion L)] :
    (Units.map (Algebra.norm (v.adicCompletion K) :
      w.1.adicCompletion L →* v.adicCompletion K)).range.index = 2 := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : CharZero (v.adicCompletion K) := charZero_adicCompletion K v
  haveI : Algebra.IsSeparable (v.adicCompletion K) (w.1.adicCompletion L) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance

  set A : ValuationSubring (w.1.adicCompletion L) := w.1.adicCompletionIntegers L with hA
  set G : Subgroup (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :=
    A.decompositionSubgroup (v.adicCompletion K) with hGdef
  have hG : G = ⊤ := decompositionSubgroup_eq_top K L v w h2
  haveI : Finite G := inferInstance
  haveI : IsCyclic G := Subgroup.isCyclic G
  letI : Fintype G := Fintype.ofFinite G
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers L w.1
  haveI : Finite (𝓞 L ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  haveI : Finite (IsLocalRing.ResidueField A) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers L w.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨hcard, -⟩ := M4aLocalCFT.fieldUnitsDecomp_herbrandQuotient_eq_card (v.adicCompletion K) A g hg

  set g' : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L := g.1 with hg'
  have hg' : ∀ σ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L, σ ∈ Subgroup.zpowers g' := by
    intro σ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨σ, hG ▸ Subgroup.mem_top σ⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [hg', ← Subgroup.coe_zpow, hk]⟩

  set N := M4aLocalCFT.fieldUnitsNorm (K := v.adicCompletion K) A with hN
  set D := M4aLocalCFT.fieldUnitsDerive (K := v.adicCompletion K) A g with hD
  set ι : (v.adicCompletion K)ˣ →* (w.1.adicCompletion L)ˣ :=
    Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) : v.adicCompletion K →* w.1.adicCompletion L)
    with hι
  set NK : (w.1.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
    Units.map (Algebra.norm (v.adicCompletion K) : w.1.adicCompletion L →* v.adicCompletion K) with hNK
  have hι_inj : Function.Injective ι :=
    Units.map_injective (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective

  have hN_apply : ∀ u : (w.1.adicCompletion L)ˣ, ((N u : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Algebra.norm (v.adicCompletion K) (u : w.1.adicCompletion L)) := by
    intro u
    rw [Algebra.norm_eq_prod_automorphisms]
    have : N u = ∏ s : G, M4aLocalCFT.fieldUnitsAct A s u := by
      rw [hN, M4aLocalCFT.fieldUnitsNorm, MonoidHom.finsetProd_apply]
    rw [this, Units.coe_prod]
    refine Fintype.prod_bijective (fun s : G => s.1) ⟨Subtype.val_injective, fun σ => ⟨⟨σ, hG ▸ Subgroup.mem_top σ⟩, rfl⟩⟩ _ _ (fun s => ?_)
    rfl
  have hD_apply : ∀ t : (w.1.adicCompletion L)ˣ, D t = Units.map (g' : w.1.adicCompletion L →* w.1.adicCompletion L) t / t := by
    intro t
    rw [hD, M4aLocalCFT.fieldUnitsDerive, MonoidHom.div_apply]
    rfl

  have hH90 : N.ker ≤ D.range := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have hnorm : Algebra.norm (v.adicCompletion K) (u : w.1.adicCompletion L) = 1 := by
      have := hN_apply u
      rw [hu, Units.val_one, eq_comm, ← (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).map_one] at this
      exact (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective this
    obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one hg' hnorm
    refine ⟨y⁻¹, Units.ext ?_⟩
    rw [hD_apply, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val,
      map_inv₀, ← hy]
    field_simp
  have hHm1 : Nat.card (N.ker ⧸ D.range.subgroupOf N.ker) = 1 := by
    change D.range.relIndex N.ker = 1
    exact Subgroup.relIndex_eq_one.2 hH90
  rw [hHm1, mul_one] at hcard

  have hNcomp : N = ι.comp NK := by
    ext u
    rw [hN_apply u]
    simp [hι, hNK]
  have hDker : D.ker = (⊤ : Subgroup (v.adicCompletion K)ˣ).map ι := by
    rw [← MonoidHom.range_eq_map]
    ext t
    rw [MonoidHom.mem_ker, hD_apply, div_eq_one, MonoidHom.mem_range]
    constructor
    · intro ht
      have ht' : g' (t : w.1.adicCompletion L) = t := by
        have := congrArg (fun x : (w.1.adicCompletion L)ˣ => (x : w.1.adicCompletion L)) ht
        simpa using this
      have hfix : ∀ f : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L,
          f (t : w.1.adicCompletion L) = t := by
        intro f
        have hf : f ∈ MulAction.stabilizer (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
            (t : w.1.adicCompletion L) := by
          apply Subgroup.zpowers_le.2 _ (hg' f)
          rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
          exact ht'
        rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hf
        exact hf
      have hbot := (IsGalois.mem_bot_iff_fixed (F := v.adicCompletion K) (t : w.1.adicCompletion L)).2 hfix
      rw [IntermediateField.mem_bot] at hbot
      obtain ⟨c, hc⟩ := hbot
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact t.ne_zero hc.symm
      exact ⟨Units.mk0 c hc0, Units.ext (by simp [hι, hc])⟩
    · rintro ⟨c, rfl⟩
      ext
      simp [hι]
  have hH0 : Nat.card (D.ker ⧸ N.range.subgroupOf D.ker) = NK.range.index := by
    change N.range.relIndex D.ker = _
    rw [hNcomp, MonoidHom.range_comp, hDker, Subgroup.relIndex_map_map_of_injective _ _ hι_inj,
      Subgroup.relIndex_top_right]
  rw [hH0] at hcard
  rw [hcard, ← hGdef, hG, Subgroup.card_top, IsGalois.card_aut_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two]

end localfield

section assembly

theorem finite_clause (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (v : HeightOneSpectrum (𝓞 K)) :
    (Units.map (Algebra.norm (v.adicCompletion K) :
        L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range.index ∣ 2 := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  have hdim : pb.dim = 2 := by rw [← pb.finrank, h2]
  obtain ⟨w⟩ := exists_extension K L v
  by_cases hsplit : ∃ r : v.adicCompletion K,
      r ^ 2 + algebraMap K (v.adicCompletion K) (qa pb) * r + algebraMap K (v.adicCompletion K) (qb pb) = 0
  · obtain ⟨r, hr⟩ := hsplit
    rw [range_norm_eq_top_of_root (v.adicCompletion K) pb hdim two_ne_zero r hr, Subgroup.index_top]
    exact one_dvd _
  · push Not at hsplit
    have hinj : Function.Injective (phi K L v w) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      by_contra hz0
      obtain ⟨u, rfl⟩ := isUnit_of_no_root (v.adicCompletion K) pb hdim hsplit z hz0
      exact (Units.map (phi K L v w : L ⊗[K] v.adicCompletion K →* w.1.adicCompletion L) u).ne_zero hz
    have hE : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = 2 := by
      rw [TensorProduct.finrank_rightAlgebra, h2]
    have hle := finrank_le K L v w h2
    have hge : 2 ≤ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) :=
      hE ▸ LinearMap.finrank_le_finrank_of_injective (f := (phi K L v w).toLinearMap) hinj
    have hLw : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 2 := le_antisymm hle hge
    haveI : Algebra.IsQuadraticExtension (v.adicCompletion K) (w.1.adicCompletion L) :=
      { finrank_eq_two' := hLw }
    have hbij : Function.Bijective (phi K L v w) :=
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (phi K L v w).toLinearMap)
        (hE.trans hLw.symm)).1 hinj⟩
    rw [range_norm_eq_of_algEquiv (AlgEquiv.ofBijective (phi K L v w) hbij),
      index_range_norm_local K L v w h2]

theorem infinite_clause (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (w : InfinitePlace K) :
    (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range.index ∣ 2 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hE : Module.finrank w.Completion (L ⊗[K] w.Completion) = 2 := by
    rw [TensorProduct.finrank_rightAlgebra, h2]
  have hdvd := Subgroup.index_dvd_of_le (sq_range_le_norm_range w.Completion (L ⊗[K] w.Completion) hE)
  rcases w.isReal_or_isComplex with hw | hw
  · rwa [sq_range_index_real w.Completion (InfinitePlace.Completion.ringEquivRealOfIsReal hw)] at hdvd
  · rw [sq_range_eq_top_complex w.Completion (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw),
      Subgroup.index_top] at hdvd
    exact hdvd.trans (one_dvd 2)

end assembly

end QuadNormIndex

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      (Units.map (Algebra.norm (v.adicCompletion K) :
          L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range.index ∣ 2) ∧
    (∀ w : InfinitePlace K,
      (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range.index ∣ 2) :=
  ⟨fun v => QuadNormIndex.finite_clause K L h2 v, fun w => QuadNormIndex.infinite_clause K L h2 w⟩

end S_NumberField_index_range_norm_dvd_two_of_finrank_eq_two
end P2MW
export P2MW.S_NumberField_index_range_norm_dvd_two_of_finrank_eq_two (solution)
