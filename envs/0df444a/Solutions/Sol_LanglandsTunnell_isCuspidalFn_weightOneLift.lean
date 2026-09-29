-- Prove2me | solution 1 for LanglandsTunnell.isCuspidalFn_weightOneLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0f90ce7f-882c-504a-8cbf-2dcd9b035ac4

import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Theorems.Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.NumberTheory.Modular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_isCuspidalFn_weightOneLift
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private def deltaArch (h : GL (Fin 2) ℝ) : ℂ :=
  ((⇑CuspForm.discriminant) ∣[(12 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (-5 : ℤ)

private theorem deltaArch_def (h : GL (Fin 2) ℝ) :
    deltaArch h = ((⇑CuspForm.discriminant) ∣[(12 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (-5 : ℤ) :=
  rfl

private theorem deltaArch_sl_mul (γ : SL(2, ℤ)) (h : GL (Fin 2) ℝ) :
    deltaArch ((γ : GL (Fin 2) ℝ) * h) = deltaArch h := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  unfold deltaArch
  rw [SlashAction.slash_mul, SlashInvariantForm.slash_action_eqn CuspForm.discriminant _ hγ]
  congr 2
  rw [map_mul, Units.val_mul]
  have : ((γ : GL (Fin 2) ℝ).det.val : ℝ) = 1 := by
    simp
  rw [this, one_mul]

private theorem slash_scalar (c : GL (Fin 2) ℝ) (r : ℝ) (hr : 0 < r)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    (⇑CuspForm.discriminant) ∣[(12 : ℤ)] c = fun z => ((r ^ 10 : ℝ) : ℂ) * CuspForm.discriminant z := by
  have h00 : c 0 0 = r := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = r := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  have hdet : c.det.val = r * r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < c.det.val := by rw [hdet]; positivity
  have hsmul : ∀ z : ℍ, c • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos, num, denom, h00, h01, h10, h11]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    rw [zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ hr']
  funext z
  rw [ModularForm.slash_apply, σ, if_pos hdetpos, hsmul z, hdet, denom, h10, h11]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, zero_mul, zero_add]
  rw [abs_of_pos (by positivity : 0 < r * r)]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp

private theorem deltaArch_scalar_mul (c h : GL (Fin 2) ℝ) (r : ℝ) (hr : 0 < r)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    deltaArch (c * h) = deltaArch h := by
  have hdet : c.det.val = r * r := by
    have h00 : c 0 0 = r := by
      have := congr_fun (congr_fun hc 0) 0; simpa using this
    have h01 : c 0 1 = 0 := by
      have := congr_fun (congr_fun hc 0) 1; simpa using this
    have h10 : c 1 0 = 0 := by
      have := congr_fun (congr_fun hc 1) 0; simpa using this
    have h11 : c 1 1 = r := by
      have := congr_fun (congr_fun hc 1) 1; simpa using this
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  unfold deltaArch
  rw [SlashAction.slash_mul, slash_scalar c r hr hc]
  have hfun : (fun z => ((r ^ 10 : ℝ) : ℂ) * CuspForm.discriminant z)
      = ((r ^ 10 : ℝ) : ℂ) • (⇑CuspForm.discriminant) := by
    funext z; simp [smul_eq_mul]
  rw [hfun, ModularForm.smul_slash, σ_ofReal, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mul, hdet]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hh : ((h.det.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.det.ne_zero
  push_cast
  field_simp

private theorem deltaArch_one : deltaArch 1 = CuspForm.discriminant UpperHalfPlane.I := by
  simp [deltaArch, SlashAction.slash_one]

private theorem deltaArch_one_ne_zero : deltaArch 1 ≠ 0 := by
  rw [deltaArch_one]
  exact ModularForm.discriminant_ne_zero UpperHalfPlane.I

private theorem norm_deltaArch_le : ∃ C : ℝ, ∀ h : GL (Fin 2) ℝ, 0 < h.det.val → ‖deltaArch h‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (k := 12) (Γ := 𝒮ℒ) CuspForm.discriminant
  refine ⟨C, fun h hh => ?_⟩
  have hz := hC (h • UpperHalfPlane.I)
  have him : (h • UpperHalfPlane.I).im = h.det.val / Complex.normSq (denom h UpperHalfPlane.I) := by
    rw [im_smul_eq_div_normSq, abs_of_pos hh, UpperHalfPlane.I_im, mul_one]
  have hd : denom h UpperHalfPlane.I ≠ 0 := denom_ne_zero h UpperHalfPlane.I
  have hnsq : 0 < Complex.normSq (denom h UpperHalfPlane.I) := Complex.normSq_pos.mpr hd

  have hnorm : ‖deltaArch h‖ =
      ‖CuspForm.discriminant (h • UpperHalfPlane.I)‖ * (h • UpperHalfPlane.I).im ^ (6 : ℕ) := by
    rw [deltaArch, ModularForm.slash_apply, σ, if_pos hh]
    simp only [ContinuousAlgEquiv.refl_apply, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh]
    rw [him, Complex.normSq_eq_norm_sq]
    have hd0 : ‖denom h UpperHalfPlane.I‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have hdet' : (h.det.val : ℝ) ≠ 0 := hh.ne'
    rw [show (12 : ℤ) - 1 = 11 by norm_num]
    simp only [_root_.zpow_neg, zpow_ofNat]
    field_simp
  rw [hnorm]
  have himpos : 0 < (h • UpperHalfPlane.I).im := (h • UpperHalfPlane.I).im_pos
  calc ‖CuspForm.discriminant (h • UpperHalfPlane.I)‖ * (h • UpperHalfPlane.I).im ^ (6 : ℕ)
      ≤ C / (h • UpperHalfPlane.I).im ^ ((12 : ℤ) / 2 : ℝ) * (h • UpperHalfPlane.I).im ^ (6 : ℕ) := by
        gcongr
    _ = C := by
        rw [show ((12 : ℤ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

private theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

private theorem exists_mapGL_eq_of_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hpos : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ)) :
    ∃ δ : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ δ = γ := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint

  have hγ' : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j := fun i j =>
    exists_intCast_eq_of_mem_integralFiniteAdeles (by rw [← glFin_globalPoints_apply]; exact hγ i j)
  have hγinv' : ∀ i j, ∃ n : ℤ, (n : ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j :=
    fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (by
      rw [← glFin_globalPoints_apply, map_inv, map_inv]; exact hγinv i j)
  choose a ha using hγ'
  choose b hb using hγinv'
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => a i j with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => b i j with hB
  have hAmap : A.map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hA, ha]
  have hBmap : B.map (Int.castRingHom ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hB, hb]

  have hAB : A * B = 1 := by
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℚ) :=
      Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetAB : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetQ : ((A.det : ℤ) : ℚ) = ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hAmap]
    exact (RingHom.map_det (Int.castRingHom ℚ) A)
  have hdetA : A.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h1 | h1
    · exact h1
    · exfalso
      rw [← hdetQ, h1] at hpos
      norm_num at hpos
  refine ⟨⟨A, hdetA⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  change (algebraMap ℤ ℚ) (A i j) = _
  rw [← hAmap, Matrix.map_apply]
  rfl

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private def ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
    (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArchHom g = ratArch g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArch (g * g') = ratArch g * ratArch g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArch g⁻¹ = (ratArch g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_one : ratArch 1 = 1 := by rw [← ratArchHom_apply, map_one]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    ratArch u = 1 := by
  unfold ratArch
  rw [hu, map_one, map_one]

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ratArch (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) = (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

private theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) = (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

private def IsDeltaDecomp (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ)
    (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  u ∈ (productionPinsCompact ℚ).U ⊤ ∧ glFin (𝓞 ℚ) ℚ h = 1 ∧ ratArch h ∈ GLPos (Fin 2) ℝ ∧
    g = globalPoints (𝓞 ℚ) ℚ γ * h * u

private theorem deltaArch_ratArch_eq_of_isDeltaDecomp {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ γ' : GL (Fin 2) ℚ}
    {h u h' u' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (H : IsDeltaDecomp g γ h u) (H' : IsDeltaDecomp g γ' h' u') :
    deltaArch (ratArch h) = deltaArch (ratArch h') := by
  obtain ⟨hu, hh, hpos, hg⟩ := H
  obtain ⟨hu', hh', hpos', hg'⟩ := H'
  set P := globalPoints (𝓞 ℚ) ℚ with hP

  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * u' * u⁻¹ * h⁻¹ := by
    have E : P γ * (h * u) = P γ' * (h' * u') := by rw [← mul_assoc, ← mul_assoc, ← hg, ← hg']
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * u') * (h * u)⁻¹ := eq_mul_inv_of_mul_eq E
    rw [this, _root_.mul_inv_rev]
    group

  have hint : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', one_mul, inv_one, mul_one]
    exact Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hu'.1)
      (Subgroup.inv_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ hu.1))

  have harch : ratArch (P δ) = ratArch h' * (ratArch h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv,
      ratArch_eq_one_of_glArch_eq_one hu.2, ratArch_eq_one_of_glArch_eq_one hu'.2, inv_one, mul_one,
      mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((ratArch (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε, hε⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hint hdetpos

  have hh'eq : ratArch h' = (ε : GL (Fin 2) ℝ) * ratArch h := by
    rw [← ratArch_globalPoints_mapGL, hε, harch, inv_mul_cancel_right]
  rw [hh'eq, deltaArch_sl_mul]

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

open scoped Classical in

private def deltaLiftFn (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), IsDeltaDecomp g γ h u
    then deltaArch (ratArch H.choose_spec.choose) else 0

private theorem deltaLiftFn_eq {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ : GL (Fin 2) ℚ}
    {h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (H : IsDeltaDecomp g γ h u) :
    deltaLiftFn g = deltaArch (ratArch h) := by
  have hex : ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), IsDeltaDecomp g γ h u :=
    ⟨γ, h, u, H⟩
  unfold deltaLiftFn
  rw [dif_pos hex]
  exact deltaArch_ratArch_eq_of_isDeltaDecomp hex.choose_spec.choose_spec.choose_spec H

private theorem deltaLiftFn_of_not {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hg : ¬ ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), IsDeltaDecomp g γ h u) :
    deltaLiftFn g = 0 := by
  unfold deltaLiftFn
  rw [dif_neg hg]

private theorem deltaLiftFn_globalPoints_mul
    (SA : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), IsDeltaDecomp g γ h u)
    (γ₀ : GL (Fin 2) ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    deltaLiftFn (globalPoints (𝓞 ℚ) ℚ γ₀ * g) = deltaLiftFn g := by
  obtain ⟨γ, h, u, H⟩ := SA g
  have H' : IsDeltaDecomp (globalPoints (𝓞 ℚ) ℚ γ₀ * g) (γ₀ * γ) h u := by
    refine ⟨H.1, H.2.1, H.2.2.1, ?_⟩
    rw [H.2.2.2, map_mul]
    simp only [mul_assoc]
  rw [deltaLiftFn_eq H', deltaLiftFn_eq H]

private theorem deltaLiftFn_mul_of_mem_U
    (SA : ∀ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ),
      ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), IsDeltaDecomp g γ h u)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) {u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U ⊤) :
    deltaLiftFn (g * u₀) = deltaLiftFn g := by
  obtain ⟨γ, h, u, H⟩ := SA g
  have H' : IsDeltaDecomp (g * u₀) γ h (u * u₀) := by
    refine ⟨Subgroup.mul_mem _ H.1 hu₀, H.2.1, H.2.2.1, ?_⟩
    rw [H.2.2.2]
    simp only [mul_assoc]
  rw [deltaLiftFn_eq H', deltaLiftFn_eq H]

private theorem isDeltaDecomp_one : IsDeltaDecomp 1 1 1 1 := by
  refine ⟨Subgroup.one_mem _, map_one _, ?_, by rw [map_one, one_mul, one_mul]⟩
  rw [ratArch_one]
  exact Subgroup.one_mem _

private theorem deltaLiftFn_one : deltaLiftFn 1 = deltaArch 1 := by
  rw [deltaLiftFn_eq isDeltaDecomp_one, ratArch_one]

private theorem deltaLiftFn_one_ne_zero : deltaLiftFn 1 ≠ 0 := by
  rw [deltaLiftFn_one]
  exact deltaArch_one_ne_zero

private theorem exists_isDeltaDecomp_of_strongApprox {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hSA : ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      u ∈ (productionPinsCompact ℚ).U ⊤ ∧ glFin (𝓞 ℚ) ℚ h = 1 ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h)) ∈ GLPos (Fin 2) ℝ) ∧
        g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)), IsDeltaDecomp g γ h u := by
  obtain ⟨γ, h, u, hu, hh, harch, hg⟩ := hSA
  exact ⟨γ, h, u, hu, hh, harch default (isReal_rat_infinitePlace default), hg⟩

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm NumberField.AdelicLevel MeasureTheory Complex
p2m_open "UpperHalfPlane~I"
open scoped MatrixGroups ModularForm Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

private abbrev archPart (k : 𝔾) : 𝔾 := adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ k)

private abbrev finPart (k : 𝔾) : 𝔾 := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ k)

private theorem eq_of_glArch_eq_of_glFin_eq {g g' : 𝔾} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ g')
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g') : g = g' := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) hf) i) j
    rwa [glFin_apply, glFin_apply] at this

private theorem glArch_archPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (archPart k) = glArch (𝓞 ℚ) ℚ k :=
  glArch_adelicArchGLIncl ℚ _

private theorem glFin_archPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (archPart k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem glArch_finPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (finPart k) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

private theorem glFin_finPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (finPart k) = glFin (𝓞 ℚ) ℚ k :=
  AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _

private theorem archPart_mul_finPart (k : 𝔾) : archPart k * finPart k = k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, glArch_archPart, glArch_finPart, mul_one])
    (by rw [map_mul, glFin_archPart, glFin_finPart, one_mul])

private theorem archPart_mul_finPart_comm (k k' : 𝔾) : archPart k * finPart k' = finPart k' * archPart k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, glArch_archPart, glArch_finPart, mul_one, one_mul])
    (by rw [map_mul, map_mul, glFin_archPart, glFin_finPart, one_mul, mul_one])

private theorem finPart_eq_self_of_glArch_eq_one {u : 𝔾} (hu : glArch (𝓞 ℚ) ℚ u = 1) : finPart u = u :=
  eq_of_glArch_eq_of_glFin_eq (by rw [glArch_finPart, hu]) (glFin_finPart u)

private theorem ratArch_archPart (k : 𝔾) : ratArch (archPart k) = ratArch k := by
  unfold ratArch
  rw [glArch_archPart]

private theorem mem_U_top_iff (u : 𝔾) :
    u ∈ (productionPinsCompact ℚ).U ⊤ ↔ glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ ∧ glArch (𝓞 ℚ) ℚ u = 1 :=
  Iff.rfl

private theorem finPart_mem_U_top {k : 𝔾} (hk : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤) :
    finPart k ∈ (productionPinsCompact ℚ).U ⊤ :=
  (mem_U_top_iff _).mpr ⟨by rwa [glFin_finPart], glArch_finPart k⟩

private theorem isDeltaDecomp_mul {g₀ : 𝔾} {γ₀ : GL (Fin 2) ℚ} {h₀ u₀ : 𝔾} (H : IsDeltaDecomp g₀ γ₀ h₀ u₀) (k : 𝔾)
    (hkf : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤) (hdet : 0 < (ratArch h₀ * ratArch k).det.val) :
    IsDeltaDecomp (g₀ * k) γ₀ (h₀ * archPart k) (u₀ * finPart k) := by
  obtain ⟨hu₀, hh₀, _, hg₀⟩ := H
  refine ⟨Subgroup.mul_mem _ hu₀ (finPart_mem_U_top hkf), ?_, ?_, ?_⟩
  · rw [map_mul, hh₀, glFin_archPart, mul_one]
  · show 0 < (ratArch (h₀ * archPart k)).det.val
    rwa [ratArch_mul, ratArch_archPart]
  · have hu₀' : finPart u₀ = u₀ := finPart_eq_self_of_glArch_eq_one ((mem_U_top_iff u₀).mp hu₀).2
    calc g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀ * (archPart k * finPart k) := by rw [archPart_mul_finPart, hg₀]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (finPart u₀ * archPart k) * finPart k := by rw [hu₀']; group
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (archPart k * finPart u₀) * finPart k := by rw [archPart_mul_finPart_comm]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) := by rw [hu₀']; group

private theorem deltaLiftFn_mul_eq {g₀ : 𝔾} {γ₀ : GL (Fin 2) ℚ} {h₀ u₀ : 𝔾} (H : IsDeltaDecomp g₀ γ₀ h₀ u₀) (k : 𝔾)
    (hkf : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤) (hdet : 0 < (ratArch h₀ * ratArch k).det.val) :
    deltaLiftFn (g₀ * k) = deltaArch (ratArch h₀ * ratArch k) := by
  rw [deltaLiftFn_eq (isDeltaDecomp_mul H k hkf hdet), ratArch_mul, ratArch_archPart]

private theorem continuous_ratArch : Continuous ratArch := by
  have hcont : Continuous
      (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom := by
    have : ⇑(InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
        = InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_rat_infinitePlace default) := by
      funext x; rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous
  have hmap : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom) :=
    Continuous.units_map _ ((continuous_id.matrix_map hcont) :
      Continuous fun m : Matrix (Fin 2) (Fin 2) _ => m.map _)
  exact hmap.comp ((continuous_archComponent ℚ default).comp (continuous_glArch (𝓞 ℚ) ℚ))

private theorem continuous_entry (i j : Fin 2) : Continuous fun h : GL (Fin 2) ℝ => (((h : Matrix (Fin 2) (Fin 2) ℝ) i j :
    ℝ) : ℂ) :=
  continuous_ofReal.comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_denom_I : Continuous fun h : GL (Fin 2) ℝ => denom h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ)
  exact ((continuous_entry 1 0).mul continuous_const).add (continuous_entry 1 1)

private theorem continuous_num_I : Continuous fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)
  exact ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 0 1)

private theorem continuous_det_val : Continuous fun h : GL (Fin 2) ℝ => h.det.val := by
  show Continuous fun h : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det h).val
  simp_rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.continuous_val.matrix_det

private theorem isOpen_detPos : IsOpen {h : GL (Fin 2) ℝ | 0 < h.det.val} :=
  isOpen_lt continuous_const continuous_det_val

private theorem deltaArch_eq_of_det_pos (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    deltaArch h = CuspForm.discriminant (h • UpperHalfPlane.I) * (((h.det.val : ℝ) : ℂ)) ^ (11 : ℤ)
      * denom h UpperHalfPlane.I ^ (-12 : ℤ) * (((h.det.val : ℝ) : ℂ)) ^ (-5 : ℤ) := by
  have h' : 0 < ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : ∀ w : ℂ, σ h w = w := fun w => by simp [σ, h']
  unfold deltaArch
  rw [ModularForm.slash_apply, hσ, abs_of_pos hh]
  norm_num

private theorem continuousOn_coe_smul_I :
    ContinuousOn (fun h : GL (Fin 2) ℝ => ((h • UpperHalfPlane.I : ℍ) : ℂ)) {h | 0 < h.det.val} := by
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I / denom h UpperHalfPlane.I) ?_ ?_
  · exact (continuous_num_I.div continuous_denom_I fun h => denom_ne_zero h _).continuousOn
  · intro h hh
    exact coe_smul_of_det_pos hh _

private theorem continuousOn_discriminant_smul_I :
    ContinuousOn (fun h : GL (Fin 2) ℝ => CuspForm.discriminant (h • UpperHalfPlane.I)) {h | 0 < h.det.val} := by
  have hΔ : Continuous (⇑CuspForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'.continuous
  have hsmul : ContinuousOn (fun h : GL (Fin 2) ℝ => (h • UpperHalfPlane.I : ℍ)) {h | 0 < h.det.val} :=
    UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr continuousOn_coe_smul_I
  exact hΔ.comp_continuousOn hsmul

private theorem continuousOn_deltaArch : ContinuousOn deltaArch {h : GL (Fin 2) ℝ | 0 < h.det.val} := by
  have hdet : Continuous fun h : GL (Fin 2) ℝ => (((h.det.val : ℝ) : ℂ)) := continuous_ofReal.comp continuous_det_val
  have hdet0 : ∀ h : GL (Fin 2) ℝ, (((h.det.val : ℝ) : ℂ)) ≠ 0 := fun h => by exact_mod_cast h.det.ne_zero
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ => CuspForm.discriminant (h • UpperHalfPlane.I)
      * (((h.det.val : ℝ) : ℂ)) ^ (11 : ℤ) * denom h UpperHalfPlane.I ^ (-12 : ℤ) * (((h.det.val : ℝ) : ℂ)) ^ (-5 : ℤ))
    ?_ fun h hh => deltaArch_eq_of_det_pos h hh
  refine ((continuousOn_discriminant_smul_I.mul ?_).mul ?_).mul ?_
  · exact (hdet.zpow₀ _ fun h => Or.inl (hdet0 h)).continuousOn
  · exact (continuous_denom_I.zpow₀ _ fun h => Or.inl (denom_ne_zero h _)).continuousOn
  · exact (hdet.zpow₀ _ fun h => Or.inl (hdet0 h)).continuousOn

private theorem continuous_deltaLiftFn
    (SA : ∀ g : 𝔾, ∃ (γ : GL (Fin 2) ℚ) (h u : 𝔾), IsDeltaDecomp g γ h u) :
    Continuous deltaLiftFn := by
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  obtain ⟨γ₀, h₀, u₀, H⟩ := SA g₀
  have hh₀ : 0 < (ratArch h₀).det.val := H.2.2.1
  have hinner : Continuous fun g : 𝔾 => ratArch h₀ * ratArch (g₀⁻¹ * g) :=
    continuous_const.mul (continuous_ratArch.comp (continuous_const.mul continuous_id))

  let W : Set 𝔾 := {g | glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤
    ∧ 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g)).det.val}
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelOne (𝓞 ℚ) ℚ (N := ⊤) top_ne_bot).preimage
        ((continuous_glFin (𝓞 ℚ) ℚ).comp (continuous_const.mul continuous_id))
    · exact isOpen_detPos.preimage hinner
  have hg₀W : g₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g₀) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤
      rw [inv_mul_cancel, map_one]
      exact Subgroup.one_mem _
    · show 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g₀)).det.val
      rwa [inv_mul_cancel, ratArch_one, mul_one]

  have hEq : Set.EqOn deltaLiftFn (fun g => deltaArch (ratArch h₀ * ratArch (g₀⁻¹ * g))) W := by
    intro g hg
    have := deltaLiftFn_mul_eq H (g₀⁻¹ * g) hg.1 hg.2
    rwa [mul_inv_cancel_left] at this
  have hpt : ContinuousAt deltaArch (ratArch h₀ * ratArch (g₀⁻¹ * g₀)) :=
    continuousOn_deltaArch.continuousAt (isOpen_detPos.mem_nhds hg₀W.2)
  have hmodel : ContinuousAt (fun g : 𝔾 => deltaArch (ratArch h₀ * ratArch (g₀⁻¹ * g))) g₀ :=
    ContinuousAt.comp (f := fun g : 𝔾 => ratArch h₀ * ratArch (g₀⁻¹ * g)) (x := g₀) hpt hinner.continuousAt
  exact hmodel.congr ((Filter.eventuallyEq_of_mem (hWopen.mem_nhds hg₀W) hEq).symm)

private theorem norm_deltaLiftFn_le : ∃ C : ℝ, ∀ g : 𝔾, ‖deltaLiftFn g‖ ≤ C := by
  obtain ⟨C, hC⟩ := norm_deltaArch_le
  refine ⟨max C 0, fun g => ?_⟩
  by_cases H : ∃ (γ : GL (Fin 2) ℚ) (h u : 𝔾), IsDeltaDecomp g γ h u
  · obtain ⟨γ, h, u, H⟩ := H
    rw [deltaLiftFn_eq H]
    exact (hC _ H.2.2.1).trans (le_max_left _ _)
  · rw [deltaLiftFn_of_not H, norm_zero]
    exact le_max_right _ _

private theorem memLp_two_deltaLiftFn
    (SA : ∀ g : 𝔾, ∃ (γ : GL (Fin 2) ℚ) (h u : 𝔾), IsDeltaDecomp g γ h u) :
    letI := (productionPinsCompact ℚ).mS
    MemLp deltaLiftFn 2 (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) := by
  letI := (productionPinsCompact ℚ).mS
  haveI : BorelSpace 𝔾 := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : IsFiniteMeasure (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (productionPinsCompact_μ_D_pos_lt_top ℚ).2⟩
  obtain ⟨C, hC⟩ := norm_deltaLiftFn_le
  exact MemLp.of_bound (continuous_deltaLiftFn SA).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

end LanglandsTunnell.P4.I2

end

open Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem exists_borel_mul_mapGL (γ : GL (Fin 2) ℚ) :
    ∃ β : GL (Fin 2) ℚ, β ∈ AutomorphicForm.borelSubgroup ℚ ∧
      ∃ δ : SL(2, ℤ), γ = β * Matrix.SpecialLinearGroup.mapGL ℚ δ := by
  set c : ℚ := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 with hc
  set d : ℚ := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 with hd
  by_cases h0 : c = 0
  · exact ⟨γ, by rw [AutomorphicForm.mem_borelSubgroup_iff, ← hc, h0], 1, by rw [map_one, mul_one]⟩

  set r : ℚ := d / c with hr
  have hcop : IsCoprime r.num (-(r.den : ℤ)) := by
    refine IsCoprime.neg_right (Int.isCoprime_iff_gcd_eq_one.mpr ?_)
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ)
    (show ![r.num, -(r.den : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from hcop)
  have hg0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r.num := by
    have := congrFun hg 0; simpa using this
  have hg1 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -(r.den : ℤ) := by
    have := congrFun hg 1; simpa using this

  let δ : SL(2, ℤ) := Matrix.SpecialLinearGroup.transpose g * ModularGroup.S
  have hδ00 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = r.num := by
    simp [δ, Matrix.SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hg0]
  have hδ10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(r.den : ℤ) := by
    simp [δ, Matrix.SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hg1]
  refine ⟨γ * Matrix.SpecialLinearGroup.mapGL ℚ δ, ?_, δ⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩

  rw [AutomorphicForm.mem_borelSubgroup_iff, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.mul_apply,
    Fin.sum_univ_two, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, hδ00, hδ10, ← hc, ← hd]
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hnum : (r.num : ℚ) = r * r.den := (div_eq_iff hden).mp (Rat.num_div_den r)
  simp only [map_neg, eq_intCast, Int.cast_natCast]
  rw [hnum, hr]
  field_simp
  ring

end LanglandsTunnell.P4.I2

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm NumberField.AdelicLevel
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

private theorem intCast_mem_integralFiniteAdeles (n : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  have h := AdelicBox.algebraMap_mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

private theorem isLevelOneMatrix_glFin_globalPoints_mapGL (ε : SL(2, ℤ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ ⊤ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hint : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [glFin_globalPoints_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
    exact intCast_mem_integralFiniteAdeles _
  refine ⟨⟨hint, fun v => ?_⟩, fun v => ?_⟩
  · rw [idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hint 1 0 v)
  · rw [idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
      (sub_mem_integralFiniteAdeles (hint 1 1) one_mem_integralFiniteAdeles v)

private theorem glFin_globalPoints_mapGL_mem (δ : SL(2, ℤ)) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ := by
  rw [mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_glFin_globalPoints_mapGL δ, ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv]
  exact isLevelOneMatrix_glFin_globalPoints_mapGL δ⁻¹

private theorem finPart_globalPoints_mapGL_mem_U (δ : SL(2, ℤ)) :
    finPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)) ∈ (productionPinsCompact ℚ).U ⊤ :=
  finPart_mem_U_top (glFin_globalPoints_mapGL_mem δ)

private theorem ratArch_archPart_globalPoints_mapGL (δ : SL(2, ℤ)) :
    ratArch (archPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ))) = (δ : GL (Fin 2) ℝ) := by
  rw [ratArch_archPart, ratArch_globalPoints_mapGL]

private theorem det_ratArch_archPart_globalPoints_mapGL (δ : SL(2, ℤ)) :
    (ratArch (archPart (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ)))).det.val = 1 := by
  rw [ratArch_archPart_globalPoints_mapGL, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.SpecialLinearGroup.det_coe _

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane DihedralWeightOne

open scoped ModularForm MatrixGroups

namespace P2GProbe
namespace R1

variable (f : ℍ → ℂ)

private theorem weightOneArchLift_def (h : GL (Fin 2) ℝ) :
    weightOneArchLift f h = (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ) :=
  rfl

private theorem weightOneArchLift_mul_of_slash_eq (γ h : GL (Fin 2) ℝ) (hγ : f ∣[(1 : ℤ)] γ = f)
    (hdet : γ.det.val = 1) :
    weightOneArchLift f (γ * h) = weightOneArchLift f h := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, hγ]
  congr 2
  rw [map_mul, Units.val_mul, hdet, one_mul]

private theorem slash_one_scalar (c : GL (Fin 2) ℝ) (r : ℝ) (hr : 0 < r)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    f ∣[(1 : ℤ)] c = fun z => ((r⁻¹ : ℝ) : ℂ) * f z := by
  have h00 : c 0 0 = r := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = r := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  have hdet : c.det.val = r * r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < c.det.val := by rw [hdet]; positivity
  have hsmul : ∀ z : ℍ, c • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos, num, denom, h00, h01, h10, h11]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    rw [zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ hr']
  funext z
  rw [ModularForm.slash_apply, σ, if_pos hdetpos, hsmul z, denom, h10, h11]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, zero_mul, zero_add, sub_self,
    zpow_zero, mul_one, _root_.zpow_neg, zpow_one, Complex.ofReal_inv]
  ring

private theorem weightOneArchLift_scalar_mul (c h : GL (Fin 2) ℝ) (r : ℝ) (hr : 0 < r)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    weightOneArchLift f (c * h) = (r : ℂ) * weightOneArchLift f h := by
  have hdet : c.det.val = r * r := by
    have h00 : c 0 0 = r := by
      have := congr_fun (congr_fun hc 0) 0; simpa using this
    have h01 : c 0 1 = 0 := by
      have := congr_fun (congr_fun hc 0) 1; simpa using this
    have h10 : c 1 0 = 0 := by
      have := congr_fun (congr_fun hc 1) 0; simpa using this
    have h11 : c 1 1 = r := by
      have := congr_fun (congr_fun hc 1) 1; simpa using this
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, slash_one_scalar f c r hr hc]
  have hfun : (fun z => ((r⁻¹ : ℝ) : ℂ) * f z) = ((r⁻¹ : ℝ) : ℂ) • f := by
    funext z; simp [smul_eq_mul]
  rw [hfun, ModularForm.smul_slash, σ_ofReal, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mul,
    hdet]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [zpow_one]
  push_cast
  field_simp

private theorem weightOneArchLift_one : weightOneArchLift f 1 = f UpperHalfPlane.I := by
  simp [weightOneArchLift, SlashAction.slash_one]

private theorem weightOneArchLift_iwasawa (z : ℍ) (h : GL (Fin 2) ℝ)
    (hh : (h : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1]) :
    weightOneArchLift f h = (z.im : ℂ) * f z := by
  have h00 : h 0 0 = z.im := by
    have := congr_fun (congr_fun hh 0) 0; simpa using this
  have h01 : h 0 1 = z.re := by
    have := congr_fun (congr_fun hh 0) 1; simpa using this
  have h10 : h 1 0 = 0 := by
    have := congr_fun (congr_fun hh 1) 0; simpa using this
  have h11 : h 1 1 = 1 := by
    have := congr_fun (congr_fun hh 1) 1; simpa using this
  have hdet : h.det.val = z.im := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < h.det.val := by rw [hdet]; exact z.im_pos
  have hsmul : h • UpperHalfPlane.I = z := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos, num, denom, h00, h01, h10, h11]
    simp only [UpperHalfPlane.coe_I, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add,
      div_one]
    apply Complex.ext <;> simp
  unfold weightOneArchLift
  rw [ModularForm.slash_apply, σ, if_pos hdetpos, hsmul, denom, h10, h11, hdet]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, Complex.ofReal_one, zero_mul,
    zero_add, sub_self, zpow_zero, mul_one, _root_.zpow_neg, inv_one, zpow_one]
  ring

private theorem norm_weightOneArchLift_le (C : ℝ)
    (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    ‖weightOneArchLift f h‖ ≤ C * Real.sqrt h.det.val := by
  have hd : denom h UpperHalfPlane.I ≠ 0 := denom_ne_zero h UpperHalfPlane.I
  have hdn : 0 < ‖denom h UpperHalfPlane.I‖ := norm_pos_iff.mpr hd

  have him : (h • UpperHalfPlane.I).im = h.det.val / ‖denom h UpperHalfPlane.I‖ ^ 2 := by
    rw [im_smul_eq_div_normSq, abs_of_pos hh, UpperHalfPlane.I_im, mul_one,
      Complex.normSq_eq_norm_sq]
  have himpos : 0 < (h • UpperHalfPlane.I).im := (h • UpperHalfPlane.I).im_pos

  have hnorm : ‖weightOneArchLift f h‖ =
      ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val := by
    unfold weightOneArchLift
    rw [ModularForm.slash_apply, σ, if_pos hh]
    simp only [ContinuousAlgEquiv.refl_apply, sub_self, zpow_zero, mul_one, _root_.zpow_neg, zpow_one,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]

  have hsq : (h • UpperHalfPlane.I).im ^ (((1 : ℤ) : ℝ) / 2) = Real.sqrt (h • UpperHalfPlane.I).im := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hspos : 0 < Real.sqrt (h • UpperHalfPlane.I).im := Real.sqrt_pos.mpr himpos
  have hpet : ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im ≤ C := by
    have h1 := hf (h • UpperHalfPlane.I)
    rw [hsq] at h1
    calc ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im
        ≤ C / Real.sqrt (h • UpperHalfPlane.I).im * Real.sqrt (h • UpperHalfPlane.I).im :=
          mul_le_mul_of_nonneg_right h1 hspos.le
      _ = C := by field_simp

  have hsqrt_im : Real.sqrt (h • UpperHalfPlane.I).im
      = Real.sqrt h.det.val / ‖denom h UpperHalfPlane.I‖ := by
    rw [him, Real.sqrt_div hh.le, Real.sqrt_sq hdn.le]
  have hds : Real.sqrt h.det.val * Real.sqrt h.det.val = h.det.val := Real.mul_self_sqrt hh.le

  have hkey : ‖weightOneArchLift f h‖ =
      (‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im) * Real.sqrt h.det.val := by
    rw [hnorm, hsqrt_im, div_eq_mul_inv]
    calc ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val
        = ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹
            * (Real.sqrt h.det.val * Real.sqrt h.det.val) := by rw [hds]
      _ = ‖f (h • UpperHalfPlane.I)‖ * (Real.sqrt h.det.val * ‖denom h UpperHalfPlane.I‖⁻¹)
            * Real.sqrt h.det.val := by ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_right hpet (Real.sqrt_nonneg _)

end P2GProbe.R1

namespace P2GProbe
namespace R3

private theorem hasWeightOneDecomp_of_ne_bot {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : DihedralWeightOne.HasWeightOneDecomp N g := by
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ :=
    AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat hN g
  exact ⟨γ, h, u, hu, hfin, hpos default (IsTotallyReal.isReal default), hg⟩

private theorem span_243_ne_bot : Ideal.span {(243 : 𝓞 ℚ)} ≠ ⊥ := by
  have h243 : ((243 : ℕ) : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast h243

private theorem hasWeightOneDecomp_243 (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    DihedralWeightOne.HasWeightOneDecomp (Ideal.span {(243 : 𝓞 ℚ)}) g :=
  hasWeightOneDecomp_of_ne_bot span_243_ne_bot g

private theorem not_exists_not_hasWeightOneDecomp {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    ¬ ∃ g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ), ¬ DihedralWeightOne.HasWeightOneDecomp N g :=
  fun ⟨g, hg⟩ => hg (hasWeightOneDecomp_of_ne_bot hN g)

private theorem weightOneLift_eq_dif_pos {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (f : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    DihedralWeightOne.weightOneLift N f g =
      DihedralWeightOne.weightOneArchLift f
        (LanglandsTunnell.ratArchGL2 (hasWeightOneDecomp_of_ne_bot hN g).choose_spec.choose) := by
  unfold DihedralWeightOne.weightOneLift
  rw [dif_pos (hasWeightOneDecomp_of_ne_bot hN g)]

end P2GProbe.R3

namespace P2GProbe
namespace R4a

open LanglandsTunnell.P4.I2 CongruenceSubgroup

private theorem ratArchGL2_eq_ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g = ratArch g := rfl

private theorem mem_of_algebraMap_mem_idealBall {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {r : 𝓞 ℚ}
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r) ∈ idealBall (𝓞 ℚ) ℚ N) :
    r ∈ N := by
  classical
  rw [← Ideal.iInf_maxPowDividing_eq hN, Ideal.mem_iInf]
  intro v
  have h1 := h v
  rw [show (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)) v
      = algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ r) from rfl, valued_algebraMap,
    idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_le_pow_iff_mem] at h1
  exact h1

private theorem dvd_of_algebraMap_intCast_mem_idealBall {n : ℕ} (hn : n ≠ 0) {k : ℤ}
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (k : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    (n : ℤ) ∣ k := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have h' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ))
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rwa [map_intCast]
  have hmem : (k : 𝓞 ℚ) ∈ Ideal.span {(n : 𝓞 ℚ)} := mem_of_algebraMap_mem_idealBall hN h'
  have hdvd : (n : 𝓞 ℚ) ∣ (k : 𝓞 ℚ) := Ideal.mem_span_singleton.mp hmem
  have := map_dvd Rat.ringOfIntegersEquiv hdvd
  simpa using this

private theorem glFin_globalPoints_mapGL_apply (ε : SL(2, ℤ)) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((ε i j : ℤ) : ℚ) := by
  rw [glFin_globalPoints_apply]
  congr 1

private theorem mem_Gamma1_of_glFin_mem_finiteLevelOne {n : ℕ} (hn : n ≠ 0) (ε : SL(2, ℤ))
    (hε : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    ε ∈ Gamma1 n := by
  have hL := (mem_finiteLevelOne_iff.mp hε).1

  have hc : (n : ℤ) ∣ ε 1 0 := by
    apply dvd_of_algebraMap_intCast_mem_idealBall hn
    have := hL.lowerLeft
    rwa [glFin_globalPoints_mapGL_apply] at this

  have hd : (n : ℤ) ∣ ε 1 1 - 1 := by
    apply dvd_of_algebraMap_intCast_mem_idealBall hn
    have := hL.lowerRight
    rw [glFin_globalPoints_mapGL_apply] at this
    rwa [Int.cast_sub, Int.cast_one, map_sub, map_one]
  have hc' : (ε 1 0 : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hc
  have hd' : (ε 1 1 : ZMod n) = 1 := by
    have h0 : ((ε 1 1 - 1 : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hd
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at h0
    exact h0

  have hdet : ε 0 0 * ε 1 1 - ε 0 1 * ε 1 0 = 1 := by
    have := ε.det_coe
    rwa [Matrix.det_fin_two] at this
  have ha' : (ε 0 0 : ZMod n) = 1 := by
    have h1 : ((ε 0 0 * ε 1 1 - ε 0 1 * ε 1 0 : ℤ) : ZMod n) = 1 := by rw [hdet, Int.cast_one]
    push_cast at h1
    rwa [hd', hc', mul_one, mul_zero, sub_zero] at h1
  exact (Gamma1_mem n ε).mpr ⟨ha', hd', hc'⟩

private theorem finiteLevelZero_le_finiteIntegralGL2 (N : Ideal (𝓞 ℚ)) :
    finiteLevelZero (𝓞 ℚ) ℚ N ≤ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  intro g hg
  rw [mem_finiteLevelZero_iff] at hg
  show g ∈ finiteLevelZero (𝓞 ℚ) ℚ ⊤
  rw [mem_finiteLevelZero_iff]
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N m → IsLevelZeroMatrix (𝓞 ℚ) ℚ ⊤ m := fun m hm =>
    ⟨hm.integral, fun v => (hm.lowerLeft v).trans
      ((idealBound_le_one N v).trans (idealBound_top v).ge)⟩
  exact ⟨key _ hg.1, key _ hg.2⟩

private theorem weightOneArchLift_eq_of_decomps {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ γ' : GL (Fin 2) ℚ}
    {h u h' u' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u)
    (hu' : u' ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh' : glFin (𝓞 ℚ) ℚ h' = 1)
    (hpos' : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ)
    (hg' : g = globalPoints (𝓞 ℚ) ℚ γ' * h' * u') :
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)
      = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h') := by
  simp only [ratArchGL2_eq_ratArch] at hpos hpos' ⊢
  have hufin := glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu
  have hu'fin := glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu'
  have huarch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu
  have hu'arch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu'
  set P := globalPoints (𝓞 ℚ) ℚ with hP
  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * u' * u⁻¹ * h⁻¹ := by
    have E : P γ * (h * u) = P γ' * (h' * u') := by rw [← mul_assoc, ← mul_assoc, ← hg, ← hg']
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * u') * (h * u)⁻¹ := eq_mul_inv_of_mul_eq E
    rw [this, _root_.mul_inv_rev]
    group

  have hlevel : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', one_mul, inv_one, mul_one]
    exact Subgroup.mul_mem _ hu'fin (Subgroup.inv_mem _ hufin)
  have hint : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _ hlevel)

  have harch : ratArch (P δ) = ratArch h' * (ratArch h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv,
      ratArch_eq_one_of_glArch_eq_one huarch, ratArch_eq_one_of_glArch_eq_one hu'arch, inv_one,
      mul_one, mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((ratArch (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε, hε⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hint hdetpos

  have hεΓ : ε ∈ Gamma1 n := by
    apply mem_Gamma1_of_glFin_mem_finiteLevelOne hn
    rw [hε]
    exact hlevel
  have hh'eq : ratArch h' = (ε : GL (Fin 2) ℝ) * ratArch h := by
    rw [← ratArch_globalPoints_mapGL, hε, harch, inv_mul_cancel_right]
  have hεdet : ((ε : GL (Fin 2) ℝ)).det.val = 1 := by simp
  rw [hh'eq, R1.weightOneArchLift_mul_of_slash_eq f _ _ (hf ε hεΓ) hεdet]

private theorem weightOneLift_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hfin : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  have H : HasWeightOneDecomp (Ideal.span {(n : 𝓞 ℚ)}) g := ⟨γ, h, u, hu, hfin, hpos, hg⟩
  unfold DihedralWeightOne.weightOneLift
  rw [dif_pos H]
  obtain ⟨u₀, hu₀, hh₀, hpos₀, hg₀⟩ := H.choose_spec.choose_spec
  exact weightOneArchLift_eq_of_decomps hn f hf hu₀ hh₀ hpos₀ hg₀ hu hfin hpos hg

private theorem weightOneLift_mul_of_mem_U {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) {u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g * u₀) = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  have hg' : g * u₀ = globalPoints (𝓞 ℚ) ℚ γ * h * (u * u₀) := by
    rw [hg]; simp only [mul_assoc]
  rw [weightOneLift_eq hn f hf (g * u₀) γ h (u * u₀) (Subgroup.mul_mem _ hu hu₀) hfin hpos hg',
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg]

private theorem weightOneLift_globalPoints_mul {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (γ₀ : GL (Fin 2) ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ₀ * g)
      = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  have hg' : globalPoints (𝓞 ℚ) ℚ γ₀ * g = globalPoints (𝓞 ℚ) ℚ (γ₀ * γ) * h * u := by
    rw [hg, map_mul]; simp only [mul_assoc]
  rw [weightOneLift_eq hn f hf _ (γ₀ * γ) h u hu hfin hpos hg',
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg]

end P2GProbe.R4a

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 AutomorphicForm.WindowedSiegel NumberField.AdelicVolume

private theorem exists_algebraMap_eq_of_mem_integral {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

private theorem exists_intCast_eq_of_mem_integral {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integral hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

private theorem abs_eq_one_of_mem_integral {q : ℚ} (hq0 : q ≠ 0)
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hq' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q⁻¹ ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : |q| = 1 := by
  obtain ⟨a, ha⟩ := exists_intCast_eq_of_mem_integral hq
  obtain ⟨b, hb⟩ := exists_intCast_eq_of_mem_integral hq'
  have hab : a * b = 1 := by
    have : ((a * b : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, ha, hb, mul_inv_cancel₀ hq0]
    exact_mod_cast this
  rw [← ha]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h1 | h1 <;> simp [h1]

private theorem algebraMap_det_mem_integral (γ : GL (Fin 2) ℚ)
    (h : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ : ℚˣ) : ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  simp only [← glFin_globalPoints_apply]
  exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (h 0 0) (h 1 1))
    (mul_mem_integralFiniteAdeles (h 0 1) (h 1 0))

private theorem abs_det_eq_one_of_glFin_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    |((GeneralLinearGroup.det γ : ℚˣ) : ℚ)| = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint
  have hγinv' : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [map_inv, map_inv]
    exact hγinv i j
  have h1 := algebraMap_det_mem_integral γ hγ
  have h2 := algebraMap_det_mem_integral γ⁻¹ hγinv'
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  exact abs_eq_one_of_mem_integral (GeneralLinearGroup.det γ).ne_zero h1 h2

private theorem archDetNorm_default_eq (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    archDetNorm (default : InfinitePlace ℚ) g = |(ratArch g).det.val| := by
  unfold archDetNorm ratArch
  rw [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, GeneralLinearGroup.val_det_apply,
    ← Real.norm_eq_abs]
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (isReal_rat_infinitePlace (default : InfinitePlace ℚ))
  exact (hiso.norm_map_of_map_zero (map_zero _) _).symm

private theorem det_ratArch_eq_archDetNorm {n : ℕ} {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ : GL (Fin 2) ℚ}
    {h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hgint : glFin (𝓞 ℚ) ℚ g ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    (LanglandsTunnell.ratArchGL2 h).det.val = archDetNorm (default : InfinitePlace ℚ) g := by
  simp only [R4a.ratArchGL2_eq_ratArch] at hpos ⊢
  have huarch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu
  have hufin : glFin (𝓞 ℚ) ℚ u ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    R4a.finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
      (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu))
  have hγ : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    have hsplit : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) = glFin (𝓞 ℚ) ℚ g * (glFin (𝓞 ℚ) ℚ u)⁻¹ := by
      rw [hg, map_mul, map_mul, hh, mul_one, mul_inv_cancel_right]
    rw [hsplit]
    exact Subgroup.mul_mem _ hgint (Subgroup.inv_mem _ hufin)
  have habs : |(((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ)| = 1 := by
    exact_mod_cast abs_det_eq_one_of_glFin_mem_finiteIntegralGL2 hγ
  have hpos' : 0 < (ratArch h).det.val := hpos
  rw [archDetNorm_default_eq, hg, ratArch_mul, ratArch_mul, ratArch_eq_one_of_glArch_eq_one huarch,
    mul_one, map_mul, Units.val_mul, abs_mul, det_ratArch_globalPoints, habs, one_mul, abs_of_pos hpos']

private theorem norm_weightOneLift_le_of_mem_D {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hgD : g ∈ (productionPinsCompact ℚ).D) :
    ‖weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g‖ ≤ C * Real.sqrt 2 := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hh, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  rw [R4a.weightOneLift_eq hn f hf g γ h u hu hh hpos hg]
  have hC0 : 0 ≤ C := by
    have h1 := hC UpperHalfPlane.I
    rw [UpperHalfPlane.I_im, Real.one_rpow, div_one] at h1
    exact (norm_nonneg _).trans h1
  have hdetpos : 0 < (LanglandsTunnell.ratArchGL2 h).det.val := hpos
  have hD := mem_centreCutSiegelSet_iff.mp hgD
  have hwin : archDetNorm (default : InfinitePlace ℚ) g ∈ Set.Icc (1 / 2 : ℝ) 2 := hD.2.2.2 default
  have hdet := det_ratArch_eq_archDetNorm hD.1 hu hh hpos hg
  calc ‖weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)‖
      ≤ C * Real.sqrt (LanglandsTunnell.ratArchGL2 h).det.val :=
        R1.norm_weightOneArchLift_le f C hC _ hdetpos
    _ ≤ C * Real.sqrt 2 := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply Real.sqrt_le_sqrt
        rw [hdet]
        exact hwin.2

end P2GProbe.R7

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 MeasureTheory
open scoped Topology

private theorem weightOneArchLift_eq_of_det_pos (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    weightOneArchLift f h
      = f (h • UpperHalfPlane.I) * (denom h UpperHalfPlane.I)⁻¹ * ((h.det.val : ℝ) : ℂ) := by
  have h' : 0 < ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : ∀ w : ℂ, σ h w = w := fun w => by simp [σ, h']
  rw [R1.weightOneArchLift_def, ModularForm.slash_apply, hσ]
  simp

private theorem continuousOn_weightOneArchLift (f : ℍ → ℂ) (hf : Continuous f) :
    ContinuousOn (weightOneArchLift f) {h : GL (Fin 2) ℝ | 0 < h.det.val} := by
  have hsmul : ContinuousOn (fun h : GL (Fin 2) ℝ => (h • UpperHalfPlane.I : ℍ)) {h | 0 < h.det.val} :=
    UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr continuousOn_coe_smul_I
  have hdet : Continuous fun h : GL (Fin 2) ℝ => ((h.det.val : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_det_val
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ =>
      f (h • UpperHalfPlane.I) * (denom h UpperHalfPlane.I)⁻¹ * ((h.det.val : ℝ) : ℂ))
    ?_ fun h hh => weightOneArchLift_eq_of_det_pos f h hh
  exact ((hf.comp_continuousOn hsmul).mul (continuous_denom_I.inv₀ fun h => denom_ne_zero h _).continuousOn).mul
    hdet.continuousOn

private theorem mem_U_iff (N : Ideal (𝓞 ℚ)) (u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    u ∈ (productionPinsCompact ℚ).U N ↔
      glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 :=
  Iff.rfl

private theorem finPart_mem_U {N : Ideal (𝓞 ℚ)} {k : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hk : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ N) : finPart k ∈ (productionPinsCompact ℚ).U N :=
  (mem_U_iff N _).mpr ⟨by rwa [glFin_finPart], glArch_finPart k⟩

private theorem weightOneLift_mul_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {g₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ₀ : GL (Fin 2) ℚ} {h₀ u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh₀ : glFin (𝓞 ℚ) ℚ h₀ = 1)
    (hg₀ : g₀ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀) (k : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (hkf : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}))
    (hdet : 0 < (ratArch h₀ * ratArch k).det.val) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g₀ * k) = weightOneArchLift f (ratArch h₀ * ratArch k) := by
  have hu : u₀ * finPart k ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}) :=
    Subgroup.mul_mem _ hu₀ (finPart_mem_U hkf)
  have hfin : glFin (𝓞 ℚ) ℚ (h₀ * archPart k) = 1 := by
    rw [map_mul, hh₀, glFin_archPart, mul_one]
  have hpos : LanglandsTunnell.ratArchGL2 (h₀ * archPart k) ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 (h₀ * archPart k)).det.val
    rw [R4a.ratArchGL2_eq_ratArch, ratArch_mul, ratArch_archPart]
    exact hdet
  have hu₀' : finPart u₀ = u₀ := finPart_eq_self_of_glArch_eq_one ((mem_U_iff _ u₀).mp hu₀).2
  have hg : g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) :=
    calc g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀ * (archPart k * finPart k) := by
          rw [archPart_mul_finPart, hg₀]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (finPart u₀ * archPart k) * finPart k := by rw [hu₀']; group
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (archPart k * finPart u₀) * finPart k := by
          rw [archPart_mul_finPart_comm]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) := by rw [hu₀']; group
  rw [R4a.weightOneLift_eq hn f hf (g₀ * k) γ₀ _ _ hu hfin hpos hg, R4a.ratArchGL2_eq_ratArch, ratArch_mul,
    ratArch_archPart]

private theorem continuous_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    Continuous (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  obtain ⟨γ₀, h₀, u₀, hu₀, hh₀, hpos₀, hg₀⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g₀
  have hh₀pos : 0 < (ratArch h₀).det.val := by
    rw [← R4a.ratArchGL2_eq_ratArch]
    exact hpos₀
  have hinner : Continuous fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) => ratArch h₀ * ratArch (g₀⁻¹ * g) :=
    continuous_const.mul (continuous_ratArch.comp (continuous_const.mul continuous_id))
  let W : Set (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    {g | glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      ∧ 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g)).det.val}
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelOne (𝓞 ℚ) ℚ (N := Ideal.span {(n : 𝓞 ℚ)}) hN).preimage
        ((continuous_glFin (𝓞 ℚ) ℚ).comp (continuous_const.mul continuous_id))
    · exact isOpen_detPos.preimage hinner
  have hg₀W : g₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g₀) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      rw [inv_mul_cancel, map_one]
      exact Subgroup.one_mem _
    · show 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g₀)).det.val
      rwa [inv_mul_cancel, ratArch_one, mul_one]
  have hEq : Set.EqOn (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f)
      (fun g => weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ * g))) W := by
    intro g hg
    have := weightOneLift_mul_eq hn f hf hu₀ hh₀ hg₀ (g₀⁻¹ * g) hg.1 hg.2
    rwa [mul_inv_cancel_left] at this
  have hpt : ContinuousAt (weightOneArchLift f) (ratArch h₀ * ratArch (g₀⁻¹ * g₀)) :=
    (continuousOn_weightOneArchLift f hf_cont).continuousAt (isOpen_detPos.mem_nhds hg₀W.2)
  have hmodel : ContinuousAt (fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) =>
      weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ * g))) g₀ :=
    ContinuousAt.comp (f := fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) => ratArch h₀ * ratArch (g₀⁻¹ * g))
      (x := g₀) hpt hinner.continuousAt
  exact hmodel.congr ((Filter.eventuallyEq_of_mem (hWopen.mem_nhds hg₀W) hEq).symm)

private theorem memLp_two_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    letI := (productionPinsCompact ℚ).mS
    MemLp (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) 2
      (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) := by
  letI := (productionPinsCompact ℚ).mS
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : IsFiniteMeasure (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (productionPinsCompact_μ_D_pos_lt_top ℚ).2⟩
  refine MemLp.of_bound (continuous_weightOneLift hn f hf_cont hf).aestronglyMeasurable (C * Real.sqrt 2) ?_
  exact ae_restrict_of_forall_mem (measurableSet_productionPinsCompact_D ℚ)
    fun g hg => norm_weightOneLift_le_of_mem_D hn f hf C hC hg

end P2GProbe.R7

namespace P2GProbe
namespace R4a

private theorem gamma1_slash_binder_of_SL_slash (F : ℍ → ℂ)
    (h : ∀ γ ∈ CongruenceSubgroup.Gamma1 243, F ∣[(1 : ℤ)] γ = F) :
    ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 243 → F ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = F :=
  fun ε hε => by simpa [ModularForm.SL_slash] using h ε hε

end P2GProbe.R4a

namespace P2GProbe
namespace R8

open LanglandsTunnell.P4.I2 MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicBox
open scoped Manifold

attribute [local instance] NumberField.AdelicHaar.adeleBorel

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "ν₀" => ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)

private theorem coe_SL_inv (ρ : SL(2, ℤ)) : ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ((ρ : GL (Fin 2) ℝ))⁻¹ := by
  change Matrix.SpecialLinearGroup.mapGL ℝ ρ⁻¹ = (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹
  exact map_inv _ _

private theorem det_coe_SL (ρ : SL(2, ℤ)) : ((ρ : GL (Fin 2) ℝ)).det.val = 1 := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ ρ).det.val = 1
  rw [Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]

private def nArch (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by rw [Matrix.det_fin_two_of]; simp)

private theorem nArch_apply (t : ℝ) : ((nArch t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] := rfl

private theorem det_nArch (t : ℝ) : (nArch t).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det !![(1 : ℝ), t; 0, 1] = _
  rw [Matrix.det_fin_two_of]; ring

private theorem det_pos_nArch (t : ℝ) : 0 < (nArch t).det.val := by
  rw [det_nArch]; exact one_pos

private theorem denom_nArch (t : ℝ) (z : ℍ) : denom (nArch t) z = 1 := by
  simp [denom, nArch_apply]

private theorem num_nArch (t : ℝ) (z : ℍ) : num (nArch t) z = (z : ℂ) + t := by
  simp [num, nArch_apply]

private theorem nArch_smul (t : ℝ) (z : ℍ) : nArch t • z = t +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_pos_nArch t), num_nArch, denom_nArch, div_one, coe_vadd, add_comm]

private theorem slash_nArch (F : ℍ → ℂ) (t : ℝ) : F ∣[(1 : ℤ)] nArch t = fun z => F (t +ᵥ z) := by
  have h' : 0 < ((nArch t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact det_pos_nArch t
  have hσ : ∀ w : ℂ, σ (nArch t) w = w := fun w => by simp [σ, h']
  funext z
  rw [ModularForm.slash_apply, hσ, nArch_smul, det_nArch, denom_nArch]
  simp

private theorem weightOneArchLift_SL_mul (f : ℍ → ℂ) (ρ : SL(2, ℤ)) (M : GL (Fin 2) ℝ) :
    weightOneArchLift f ((ρ : GL (Fin 2) ℝ) * M) = weightOneArchLift (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) M := by
  rw [R1.weightOneArchLift_def, R1.weightOneArchLift_def, SlashAction.slash_mul, map_mul, Units.val_mul,
    det_coe_SL, one_mul]

private theorem weightOneArchLift_nArch_mul (F : ℍ → ℂ) (t : ℝ) (H : GL (Fin 2) ℝ) (hH : 0 < H.det.val) :
    weightOneArchLift F (nArch t * H)
      = F (t +ᵥ (H • UpperHalfPlane.I : ℍ)) * (denom H UpperHalfPlane.I)⁻¹ * ((H.det.val : ℝ) : ℂ) := by
  have hG : weightOneArchLift F (nArch t * H) = weightOneArchLift (fun z => F (t +ᵥ z)) H := by
    rw [R1.weightOneArchLift_def, R1.weightOneArchLift_def, SlashAction.slash_mul, slash_nArch, map_mul,
      Units.val_mul, det_nArch, one_mul]
  rw [hG, R7.weightOneArchLift_eq_of_det_pos _ H hH]

private theorem intervalIntegral_weightOneArchLift_nArch_mul (F : ℍ → ℂ) (n : ℕ)
    (hF : ∀ z : ℍ, ∫ s in (0 : ℝ)..(n : ℝ), F (s +ᵥ z) = 0) (r : ℝ) (H : GL (Fin 2) ℝ)
    (hH : 0 < H.det.val) :
    ∫ s in (0 : ℝ)..(n : ℝ), weightOneArchLift F (nArch (r + s) * H) = 0 := by
  simp_rw [weightOneArchLift_nArch_mul F _ H hH, add_comm r, add_vadd]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hF, zero_mul, zero_mul]

private theorem gamma_le_gamma1_of_level (n : ℕ) : CongruenceSubgroup.Gamma n ≤ CongruenceSubgroup.Gamma1 n := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  exact (CongruenceSubgroup.Gamma1_mem n γ).mpr ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

private theorem slash_vadd_natCast {n : ℕ} (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (ρ : SL(2, ℤ)) (w : ℍ) :
    (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) ((n : ℝ) +ᵥ w) = (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) w := by
  have hT : ModularGroup.T ^ (n : ℤ) ∈ CongruenceSubgroup.Gamma n := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (n : ℤ) (n : ℤ) dvd_rfl
  have hκ : ρ * ModularGroup.T ^ (n : ℤ) * ρ⁻¹ ∈ CongruenceSubgroup.Gamma1 n :=
    gamma_le_gamma1_of_level n ((CongruenceSubgroup.Gamma_normal n).conj_mem _ hT ρ)
  have hfκ : f ∣[(1 : ℤ)] (ρ * ModularGroup.T ^ (n : ℤ) * ρ⁻¹) = f := hf _ hκ
  have hslash : (f ∣[(1 : ℤ)] ρ) ∣[(1 : ℤ)] (ModularGroup.T ^ (n : ℤ)) = f ∣[(1 : ℤ)] ρ := by
    rw [← SlashAction.slash_mul,
      show ρ * ModularGroup.T ^ (n : ℤ) = (ρ * ModularGroup.T ^ (n : ℤ) * ρ⁻¹) * ρ by group,
      SlashAction.slash_mul, hfκ]
  have h := congr_fun hslash w
  have hden : denom ((ModularGroup.T ^ (n : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ) w = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]
    simp
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul, hden, _root_.one_zpow, mul_one, Int.cast_natCast] at h
  exact h

private theorem intervalIntegral_slash_vadd_eq_zero {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (ρ : SL(2, ℤ)) (hρ : IsZeroAtImInfty (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ))) (z : ℍ) :
    ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hFper : ∀ w : ℍ, (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) ((n : ℝ) +ᵥ w)
      = (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) w := fun w => slash_vadd_natCast f hf ρ w
  set F : ℍ → ℂ := f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ) with hFdef

  have hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) (n : ℝ) := by
    intro w
    by_cases hw : 0 < w.im
    · have hw' : 0 < (w + (n : ℝ)).im := by simpa using hw
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw',
        UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      rw [← hFper ⟨w, hw⟩]
      congr 1
      apply UpperHalfPlane.ext
      simp [add_comm]
    · have hw₀ : w.im ≤ 0 := not_lt.mp hw
      have hw' : (w + (n : ℝ)).im ≤ 0 := by simpa using hw₀
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
        UpperHalfPlane.ofComplex_apply_of_im_nonpos hw₀]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := hf_hol.slash 1 _
  have hbdd : IsBoundedAtImInfty F := hρ.isBoundedAtImInfty

  have h0 := UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral hnpos hper hhol hbdd 0 z.im_pos
  rw [UpperHalfPlane.qExpansion_coeff_zero hnpos
      (UpperHalfPlane.analyticAt_cuspFunction_zero hnpos hper hhol hbdd) hper,
    hρ.valueAtInfty_eq_zero] at h0
  simp only [pow_zero, div_one, one_mul] at h0
  set G : ℝ → ℂ := fun u => F ⟨(u : ℂ) + z.im * Complex.I, by simpa using z.im_pos⟩ with hGdef
  have hint : ∫ u in (0 : ℝ)..(n : ℝ), G u = 0 := by
    have hn' : (1 : ℂ) / ((n : ℝ) : ℂ) ≠ 0 := one_div_ne_zero (by exact_mod_cast hn)
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h hn'
    · exact h

  have hGper : Function.Periodic G (n : ℝ) := by
    intro u
    simp only [hGdef]
    conv_rhs => rw [← hFper]
    congr 1
    apply UpperHalfPlane.ext
    simp only [coe_vadd]
    push_cast
    ring
  have hshift : ∀ s : ℝ, F (s +ᵥ z) = G (s + z.re) := by
    intro s
    simp only [hGdef]
    congr 1
    apply UpperHalfPlane.ext
    simp only [coe_vadd]
    push_cast
    rw [add_assoc, UpperHalfPlane.re_add_im]
  simp_rw [hshift]
  rw [intervalIntegral.integral_comp_add_right G z.re, zero_add, add_comm (n : ℝ) z.re,
    hGper.intervalIntegral_add_eq z.re 0, zero_add, hint]

private def realCoord (x : 𝔸) : ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)) (x.1 default)

private theorem ratArch_unipotentGL2 (x : 𝔸) : ratArch (unipotentGL2 x) = nArch (realCoord x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp (adeleArch (𝓞 ℚ) ℚ)))
      ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    = (nArch (realCoord x) : Matrix (Fin 2) (Fin 2) ℝ) i j
  have h1 : ((1 : AdeleRing (𝓞 ℚ) ℚ).1 default) = 1 := rfl
  have h0 : ((0 : AdeleRing (𝓞 ℚ) ℚ).1 default) = 0 := rfl
  rw [unipotentGL2_coe, nArch_apply]
  fin_cases i <;> fin_cases j <;> simp [realCoord, archEval_apply, adeleArch_apply, h1, h0]

private theorem glFin_unipotentGL2_mem_integral {x : 𝔸}
    (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (unipotentGL2 x) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  have hval : (glFin (𝓞 ℚ) ℚ (unipotentGL2 x) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = !![1, x.2; 0, 1] := by
    ext i j
    rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> rfl
  have hinv : (((glFin (𝓞 ℚ) ℚ (unipotentGL2 x))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = !![1, -x.2; 0, 1] := by
    rw [← map_inv]
    refine Matrix.ext fun i j => ?_
    rw [glFin_apply]
    change ((!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 = _
    fin_cases i <;> fin_cases j <;> rfl
  have h0 := zero_mem_idealBall (R := 𝓞 ℚ) (K := ℚ) (⊤ : Ideal (𝓞 ℚ))
  have hx' : -x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    simpa using sub_mem_integralFiniteAdeles zero_mem_integralFiniteAdeles hx
  have hmem : glFin (𝓞 ℚ) ℚ (unipotentGL2 x) ∈ finiteLevelOne (𝓞 ℚ) ℚ ⊤ := by
    rw [mem_finiteLevelOne_iff, hval, hinv]
    refine ⟨⟨⟨?_, by simpa using h0⟩, by simpa using h0⟩, ⟨⟨?_, by simpa using h0⟩, by simpa using h0⟩⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hx]
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [one_mem_integralFiniteAdeles, zero_mem_integralFiniteAdeles, hx']
  exact finiteLevelOne_le_finiteLevelZero _ _ _ hmem

private def archAdele (s : ℝ) : 𝔸 :=
  (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace w)).symm s, 0)

private theorem realCoord_add_archAdele (x : 𝔸) (s : ℝ) : realCoord (x + archAdele s) = realCoord x + s := by
  change (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default))
      (x.1 default + (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).symm s)
    = (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)) (x.1 default) + s
  rw [map_add, RingEquiv.apply_symm_apply]

private theorem snd_add_archAdele (x : 𝔸) (s : ℝ) : (x + archAdele s).2 = x.2 := by
  change x.2 + 0 = x.2
  exact add_zero _

private theorem continuous_archAdele : Continuous archAdele := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_rat_infinitePlace w)).symm.continuous

private theorem unipotentGL2_inv_coe (y : 𝔸) :
    (((unipotentGL2 y)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = !![1, -y; 0, 1] := rfl

private theorem continuous_unipotentGL2 : Continuous fun y : 𝔸 => (unipotentGL2 y : 𝔾) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id'
  · refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [continuous_neg] <;> exact continuous_const

private theorem finPart_unipotentGL2_add_archAdele (x : 𝔸) (s : ℝ) :
    finPart (unipotentGL2 (x + archAdele s)) = finPart (unipotentGL2 x) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [glArch_finPart, glArch_finPart]
  · rw [glFin_finPart, glFin_finPart]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glFin_apply, glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · rfl
    · exact snd_add_archAdele x s
    · rfl
    · rfl

private theorem exists_weightOneLift_unipotent_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {x : 𝔸} (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) {h₁ q : 𝔾}
    (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1)
    (hh₁pos : 0 < (ratArch h₁).det.val)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    ∃ ρ : SL(2, ℤ), ∀ s : ℝ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (unipotentGL2 (x + archAdele s) * (h₁ * q))
        = weightOneArchLift f (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)) := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have harch₁ : archPart h₁ = h₁ :=
    eq_of_glArch_eq_of_glFin_eq (glArch_archPart h₁) (by rw [glFin_archPart, hh₁])

  set Q : 𝔾 := finPart (unipotentGL2 x) * q with hQdef
  have hQarch : glArch (𝓞 ℚ) ℚ Q = 1 := by
    rw [hQdef, map_mul, glArch_finPart, hq, mul_one]
  have hQint : glFin (𝓞 ℚ) ℚ Q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [hQdef, map_mul, glFin_finPart]
    exact Subgroup.mul_mem _ (glFin_unipotentGL2_mem_integral hx) hqint
  obtain ⟨γ, h₀, u₀, hu₀, hh₀, hpos₀, hQ⟩ := R3.hasWeightOneDecomp_of_ne_bot hN Q
  have hh₀pos : 0 < (ratArch h₀).det.val := by
    rw [← R4a.ratArchGL2_eq_ratArch]
    exact hpos₀

  have hγint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    have hsplit : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) = glFin (𝓞 ℚ) ℚ Q * (glFin (𝓞 ℚ) ℚ u₀)⁻¹ := by
      rw [hQ, map_mul, map_mul, hh₀, mul_one, mul_inv_cancel_right]
    have hu₀int : glFin (𝓞 ℚ) ℚ u₀ ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
      R4a.finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
        (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu₀))
    rw [hsplit]
    exact Subgroup.mul_mem _ hQint (Subgroup.inv_mem _ hu₀int)

  have hprod : ratArch (globalPoints (𝓞 ℚ) ℚ γ) * ratArch h₀ = 1 := by
    have h1 : ratArch Q = 1 := ratArch_eq_one_of_glArch_eq_one hQarch
    have hu₀arch : ratArch u₀ = 1 :=
      ratArch_eq_one_of_glArch_eq_one (glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu₀)
    rwa [hQ, ratArch_mul, ratArch_mul, hu₀arch, mul_one] at h1
  have hdetγ : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    have hd : (ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val * (ratArch h₀).det.val = 1 := by
      rw [← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]
    have hpos' : 0 < (ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val := by
      rw [eq_inv_of_mul_eq_one_left hd]
      exact inv_pos.mpr hh₀pos
    rw [det_ratArch_globalPoints] at hpos'
    exact_mod_cast hpos'
  obtain ⟨ρ, hρ⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hγint hdetγ
  have hρarch : ratArch (globalPoints (𝓞 ℚ) ℚ γ) = (ρ : GL (Fin 2) ℝ) := by
    rw [← hρ, ratArch_globalPoints_mapGL]
  have hh₀arch : ratArch h₀ = ((ρ : GL (Fin 2) ℝ))⁻¹ := by
    rw [hρarch] at hprod
    exact eq_inv_of_mul_eq_one_right hprod
  refine ⟨ρ, fun s => ?_⟩

  set A : 𝔾 := archPart (unipotentGL2 (x + archAdele s)) * h₁ with hAdef
  have hAfin : glFin (𝓞 ℚ) ℚ A = 1 := by
    rw [hAdef, map_mul, glFin_archPart, hh₁, mul_one]
  have hAarch : ratArch A = nArch (realCoord x + s) * ratArch h₁ := by
    rw [hAdef, ratArch_mul, ratArch_archPart, ratArch_unipotentGL2, realCoord_add_archAdele]
  have hpoint : unipotentGL2 (x + archAdele s) * (h₁ * q) = A * Q := by
    rw [hAdef, hQdef, ← finPart_unipotentGL2_add_archAdele x s]
    calc unipotentGL2 (x + archAdele s) * (h₁ * q)
        = archPart (unipotentGL2 (x + archAdele s)) * finPart (unipotentGL2 (x + archAdele s)) * archPart h₁ * q := by
          rw [archPart_mul_finPart, harch₁]; group
      _ = archPart (unipotentGL2 (x + archAdele s)) * (archPart h₁ * finPart (unipotentGL2 (x + archAdele s))) * q := by
          rw [archPart_mul_finPart_comm h₁ (unipotentGL2 (x + archAdele s))]; group
      _ = archPart (unipotentGL2 (x + archAdele s)) * h₁ * (finPart (unipotentGL2 (x + archAdele s)) * q) := by
          rw [harch₁]; group
  set h' : 𝔾 := (globalPoints (𝓞 ℚ) ℚ γ)⁻¹ * A * globalPoints (𝓞 ℚ) ℚ γ * h₀ with hh'def
  have hdecomp : unipotentGL2 (x + archAdele s) * (h₁ * q) = globalPoints (𝓞 ℚ) ℚ γ * h' * u₀ := by
    rw [hpoint, hQ, hh'def]; group
  have hh'fin : glFin (𝓞 ℚ) ℚ h' = 1 := by
    rw [hh'def, map_mul, map_mul, map_mul, map_inv, hAfin, hh₀, mul_one, mul_one, inv_mul_cancel]
  have hh'arch : ratArch h' = ((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁) := by
    rw [hh'def, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, hρarch, hh₀arch, hAarch]
    group
  have hh'pos : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 h').det.val
    rw [R4a.ratArchGL2_eq_ratArch, hh'arch, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Units.val_inv_eq_inv_val, det_coe_SL, inv_one, one_mul, det_nArch, one_mul]
    exact hh₁pos
  rw [R4a.weightOneLift_eq hn f hf _ γ h' u₀ hu₀ hh'fin hh'pos hdecomp, R4a.ratArchGL2_eq_ratArch, hh'arch]

private theorem constantTerm_eq_zero_of_arch_mul {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hper : ∀ ρ : SL(2, ℤ), ∀ z : ℍ,
      ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0)
    {h₁ q : 𝔾} (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1) (hh₁pos : 0 < (ratArch h₁).det.val)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    constantTerm ν₀ (fun x => unipotentGL2 x) (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) (h₁ * q) = 0 := by
  haveI : BorelSpace 𝔸 := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : IsProbabilityMeasure ν₀ := isProbabilityMeasure_cond_adelicBox ℚ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set φ : 𝔾 → ℂ := weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f with hφdef
  set K : ℝ → 𝔸 → ℂ := fun s x => φ (unipotentGL2 (x + archAdele s) * (h₁ * q)) with hKdef

  have hA : ∀ s : ℝ, constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = ∫ x, K s x ∂ν₀ := by
    intro s
    rw [← AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul ℚ (φ := φ)
      (fun k g => R4a.weightOneLift_globalPoints_mul hn f hf (unipotentGL2 k) g) (archAdele s) (h₁ * q)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ (unipotentGL2 x * (unipotentGL2 (archAdele s) * (h₁ * q))) = φ (unipotentGL2 (x + archAdele s) * (h₁ * q))
    rw [← mul_assoc, ← unipotentGL2_add]

  have hB : ∀ x : 𝔸, x ∈ adelicBox ℚ → ∫ s in (0 : ℝ)..(n : ℝ), K s x = 0 := by
    intro x hx
    obtain ⟨ρ, hρ⟩ := exists_weightOneLift_unipotent_eq hn f hf hx.2 hh₁ hh₁pos hq hqint
    have hK : ∀ s : ℝ, K s x
        = weightOneArchLift (f ∣[(1 : ℤ)] ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) (nArch (realCoord x + s) * ratArch h₁) := by
      intro s
      rw [hKdef, hφdef]
      show weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (unipotentGL2 (x + archAdele s) * (h₁ * q)) = _
      rw [hρ s, ← coe_SL_inv, weightOneArchLift_SL_mul]
    simp_rw [hK]
    exact intervalIntegral_weightOneArchLift_nArch_mul _ n (hper ρ⁻¹) (realCoord x) (ratArch h₁) hh₁pos

  have hKcont : Continuous (Function.uncurry K) := by
    have h1 : Continuous fun p : ℝ × 𝔸 => p.2 + archAdele p.1 :=
      continuous_snd.add (continuous_archAdele.comp continuous_fst)
    have h2 : Continuous fun p : ℝ × 𝔸 => (unipotentGL2 (p.2 + archAdele p.1) : 𝔾) * (h₁ * q) :=
      (continuous_unipotentGL2.comp h1).mul continuous_const
    exact (R7.continuous_weightOneLift hn f hf_cont hf).comp h2
  have hKbound : ∀ s : ℝ, ∀ x : 𝔸, x ∈ adelicBox ℚ → ‖K s x‖ ≤ C * Real.sqrt (ratArch h₁).det.val := by
    intro s x hx
    obtain ⟨ρ, hρ⟩ := exists_weightOneLift_unipotent_eq hn f hf hx.2 hh₁ hh₁pos hq hqint
    have hK : K s x = weightOneArchLift f (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)) := hρ s
    have hdet : 0 < (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)).det.val := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, det_coe_SL, inv_one,
        one_mul, det_nArch, one_mul]
      exact hh₁pos
    have hdet' : (((ρ : GL (Fin 2) ℝ))⁻¹ * (nArch (realCoord x + s) * ratArch h₁)).det.val = (ratArch h₁).det.val := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, det_coe_SL, inv_one,
        one_mul, det_nArch, one_mul]
    rw [hK]
    have := R1.norm_weightOneArchLift_le f C hC _ hdet
    rwa [hdet'] at this
  have hmeas : MeasurableSet (adelicBox ℚ) := measurableSet_adelicBox ℚ
  have hae : ∀ᵐ p : ℝ × 𝔸 ∂(volume.restrict (Set.Ioc (0 : ℝ) n)).prod ν₀, p ∈ Prod.snd ⁻¹' adelicBox ℚ :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (hmeas.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ => ProbabilityTheory.ae_cond_mem hmeas)
  have hint : Integrable (Function.uncurry K) ((volume.restrict (Set.Ioc (0 : ℝ) n)).prod ν₀) := by
    refine memLp_one_iff_integrable.mp
      (MemLp.of_bound hKcont.aestronglyMeasurable (C * Real.sqrt (ratArch h₁).det.val) ?_)
    filter_upwards [hae] with p hp
    exact hKbound p.1 p.2 hp

  have hswap : ∫ s in (0 : ℝ)..(n : ℝ), ∫ x, K s x ∂ν₀ = ∫ x, (∫ s in (0 : ℝ)..(n : ℝ), K s x) ∂ν₀ := by
    rw [intervalIntegral.integral_of_le hnpos.le]
    simp_rw [intervalIntegral.integral_of_le hnpos.le]
    exact integral_integral_swap hint
  have hinner : ∫ x, (∫ s in (0 : ℝ)..(n : ℝ), K s x) ∂ν₀ = 0 := by
    calc ∫ x, (∫ s in (0 : ℝ)..(n : ℝ), K s x) ∂ν₀ = ∫ _x, (0 : ℂ) ∂ν₀ := by
          refine integral_congr_ae ?_
          filter_upwards [ProbabilityTheory.ae_cond_mem hmeas] with x hx
          exact hB x hx
      _ = 0 := integral_zero _ _
  have hCT : ∫ s in (0 : ℝ)..(n : ℝ), constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q)
      = ∫ s in (0 : ℝ)..(n : ℝ), ∫ x, K s x ∂ν₀ :=
    intervalIntegral.integral_congr fun s _ => hA s
  have hconst : ∫ s in (0 : ℝ)..(n : ℝ), constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q)
      = ((n : ℝ) : ℂ) * constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hmain : ((n : ℝ) : ℂ) * constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = 0 := by
    rw [← hconst, hCT, hswap, hinner]
  have hn' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  exact (mul_eq_zero.mp hmain).resolve_left hn'

private theorem constantTerm_weightOneLift_eq_zero {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hper : ∀ ρ : SL(2, ℤ), ∀ z : ℍ,
      ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0)
    (g : 𝔾) :
    constantTerm ν₀ (fun x => unipotentGL2 x) (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) g = 0 := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hh, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  have hhpos : 0 < (ratArch h).det.val := by
    rw [← R4a.ratArchGL2_eq_ratArch]
    exact hpos
  obtain ⟨β, hβ, δ, hγ⟩ := exists_borel_mul_mapGL γ
  set k : 𝔾 := globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ) with hk
  have hg' : g = globalPoints (𝓞 ℚ) ℚ β * (k * h * u) := by
    rw [hg, hγ, map_mul, hk]
    simp only [mul_assoc]
  rw [hg', AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup ℚ
    (φ := weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f)
    (fun γ' _ h' => R4a.weightOneLift_globalPoints_mul hn f hf γ' h') hβ]
  have harch : archPart h = h :=
    eq_of_glArch_eq_of_glFin_eq (glArch_archPart h) (by rw [glFin_archPart, hh])
  have hsplit : k * h * u = archPart k * h * (finPart k * u) := by
    calc k * h * u = archPart k * finPart k * archPart h * u := by rw [archPart_mul_finPart, harch]
      _ = archPart k * (archPart h * finPart k) * u := by rw [archPart_mul_finPart_comm h k]; group
      _ = archPart k * h * (finPart k * u) := by rw [harch]; group
  rw [hsplit]
  refine constantTerm_eq_zero_of_arch_mul hn f hf_cont hf C hC hper ?_ ?_ ?_ ?_
  · rw [map_mul, glFin_archPart, one_mul, hh]
  · rw [ratArch_mul, map_mul, Units.val_mul, det_ratArch_archPart_globalPoints_mapGL, one_mul]
    exact hhpos
  · rw [map_mul, glArch_finPart, glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu, mul_one]
  · rw [map_mul, glFin_finPart]
    exact Subgroup.mul_mem _ (finiteLevelOne_le_finiteLevelZero _ _ _ (glFin_globalPoints_mapGL_mem δ))
      (R4a.finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
        (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu)))

private theorem isCuspidalFn_weightOneLift_of_period {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hper : ∀ ρ : SL(2, ℤ), ∀ z : ℍ,
      ∫ s in (0 : ℝ)..(n : ℝ), (f ∣[(1 : ℤ)] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0) :
    IsCuspidalFn ν₀ (fun x => unipotentGL2 x) (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) :=
  fun g => constantTerm_weightOneLift_eq_zero hn f hf_cont hf C hC hper g

private theorem isCuspidalFn_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty (f ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ))) :
    @IsCuspidalFn _ (productionPinsCompact ℚ).nS _ _ (productionPinsCompact ℚ).ν unipotentGL2
      (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) :=
  isCuspidalFn_weightOneLift_of_period hn f hf_hol.continuous hf C hC
    (fun ρ z => intervalIntegral_slash_vadd_eq_zero hn f hf_hol hf ρ (hzero ρ) z)

end P2GProbe.R8

end

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne in
open scoped ModularForm MatrixGroups Manifold in
theorem solution
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty (f ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ))) :
    @IsCuspidalFn _ (productionPinsCompact ℚ).nS _ _ (productionPinsCompact ℚ).ν unipotentGL2
      (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  exact P2GProbe.R8.isCuspidalFn_weightOneLift hn f hf_hol hf C hC hzero

end S_LanglandsTunnell_isCuspidalFn_weightOneLift
end P2MW
export P2MW.S_LanglandsTunnell_isCuspidalFn_weightOneLift (solution)
