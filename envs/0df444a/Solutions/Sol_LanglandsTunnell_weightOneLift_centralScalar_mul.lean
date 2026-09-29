-- Prove2me | solution 1 for LanglandsTunnell.weightOneLift_centralScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bb1c49a0-bd0d-564b-8b39-4af3556f8d19

import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_weightOneLift_centralScalar_mul
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

end LanglandsTunnell.P4.I2

end

open Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

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

end P2GProbe.R1

namespace P2GProbe
namespace R3

private theorem hasWeightOneDecomp_of_ne_bot {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : DihedralWeightOne.HasWeightOneDecomp N g := by
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ :=
    AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat hN g
  exact ⟨γ, h, u, hu, hfin, hpos default (IsTotallyReal.isReal default), hg⟩

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

end P2GProbe.R7

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 MeasureTheory
open scoped Topology

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

end P2GProbe.R7

end

namespace P2GProbe
namespace C1

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane
open DihedralWeightOne RatIdele Rat.HeightOneSpectrum LanglandsTunnell.P4.I2 CongruenceSubgroup
open NumberField.AdelicVolume
open scoped ModularForm MatrixGroups

noncomputable section

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

private def rhoUnit (x : (𝔸ℚ)ˣ) : ℚˣ := Units.mk0 (RatIdele.ρ x) (ρ_ne_zero x)

private theorem coe_rhoUnit (x : (𝔸ℚ)ˣ) : ((rhoUnit x : ℚˣ) : ℚ) = RatIdele.ρ x := rfl

private def principal (q : ℚˣ) : (𝔸ℚ)ˣ := Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q

private def unitPart (x : (𝔸ℚ)ˣ) : (𝔸ℚ)ˣ := (principal (rhoUnit x))⁻¹ * x

private theorem principal_mul_unitPart (x : (𝔸ℚ)ˣ) : principal (rhoUnit x) * unitPart x = x :=
  mul_inv_cancel_left _ _

private theorem rho_principal' (q : ℚˣ) : RatIdele.ρ (principal q) = (q : ℚ) := ρ_principal q

private theorem rho_inv_principal (q : ℚˣ) : RatIdele.ρ (principal q)⁻¹ = ((q : ℚ))⁻¹ := by
  have h := ρ_mul (principal q)⁻¹ (principal q)
  rw [inv_mul_cancel, ρ_one, rho_principal'] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem rho_unitPart (x : (𝔸ℚ)ˣ) : RatIdele.ρ (unitPart x) = 1 := by
  unfold unitPart
  rw [ρ_mul, rho_inv_principal, coe_rhoUnit, inv_mul_cancel₀ (ρ_ne_zero x)]

private theorem principal_inv (q : ℚˣ) : (principal q)⁻¹ = principal q⁻¹ :=
  (map_inv (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ)) q).symm

private theorem unitResidue_unitPart (n : ℕ) [NeZero n] (x : (𝔸ℚ)ˣ) :
    unitResidue n (unitPart x) = unitResidue n x := by
  unfold unitPart
  rw [map_mul, principal_inv, principal, unitResidue_principal, one_mul]

private theorem archCoord_unitPart_pos (x : (𝔸ℚ)ˣ) : 0 < archCoord (unitPart x) := by
  have h := (ρ_spec (unitPart x)).2
  rwa [rho_unitPart, Rat.cast_one, mul_one] at h

private theorem snd_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((unitPart x : 𝔸ℚ)).2 v = unitAt v (unitPart x) := by
  unfold RatIdele.unitAt
  rw [rho_unitPart, map_one, inv_one, mul_one]

private theorem valued_snd_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((unitPart x : 𝔸ℚ)).2 v) = 1 := by
  rw [snd_unitPart]; exact valued_unitAt v (unitPart x)

private theorem valued_snd_inv_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v) = 1 := by
  have h := valued_snd_inv_mul (unitPart x) v
  rwa [valued_snd_unitPart, mul_one] at h

private theorem snd_unitPart_mem_integral (x : (𝔸ℚ)ˣ) :
    ((unitPart x : 𝔸ℚ)).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_snd_unitPart x v).le

private theorem snd_inv_unitPart_mem_integral (x : (𝔸ℚ)ˣ) :
    (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_snd_inv_unitPart x v).le

private theorem snd_unitPart_mul_snd_inv (x : (𝔸ℚ)ˣ) :
    ((unitPart x : 𝔸ℚ)).2 * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = 1 := by
  show ((unitPart x : 𝔸ℚ) * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ)).2 = (1 : 𝔸ℚ).2
  rw [Units.mul_inv]

private theorem distribHaarChar_eq_unitPart
    (hprin : ∀ q : ℚˣ,
      MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) = 1)
    (x : (𝔸ℚ)ˣ) :
    MeasureTheory.distribHaarChar 𝔸ℚ x = MeasureTheory.distribHaarChar 𝔸ℚ (unitPart x) := by
  have h1 : MeasureTheory.distribHaarChar 𝔸ℚ (principal (rhoUnit x)) = 1 := hprin (rhoUnit x)
  conv_lhs => rw [← principal_mul_unitPart x]
  rw [map_mul, h1, one_mul]

private theorem norm_snd_unitPart (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ‖((unitPart x : 𝔸ℚ)).2 v‖ = 1 := by
  rw [FinitePlace.norm_def, valued_snd_unitPart, map_one, NNReal.coe_one]

private theorem norm_fst_unitPart (x : (𝔸ℚ)ˣ) :
    ‖((unitPart x : 𝔸ℚ)).1 Rat.infinitePlace‖ = archCoord (unitPart x) := by
  have hiso := (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).isometry
  have h0 : InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
  rw [← hiso.norm_map_of_map_zero h0, Real.norm_eq_abs]
  exact abs_of_pos (archCoord_unitPart_pos x)

private theorem coe_distribHaarChar_unitPart
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (x : (𝔸ℚ)ˣ) :
    (MeasureTheory.distribHaarChar 𝔸ℚ (unitPart x) : ℝ) = archCoord (unitPart x) := by
  rw [hprod (unitPart x),
    finprod_eq_one_of_forall_eq_one (norm_snd_unitPart x), mul_one, Fintype.prod_unique,
    show (default : InfinitePlace ℚ) = Rat.infinitePlace from Subsingleton.elim _ _, norm_fst_unitPart]
  have hmult : (Rat.infinitePlace).mult = 1 := by
    simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
  rw [hmult, pow_one]

private theorem coe_distribHaarChar_eq_archCoord
    (hprin : ∀ q : ℚˣ,
      MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) = 1)
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (x : (𝔸ℚ)ˣ) :
    (MeasureTheory.distribHaarChar 𝔸ℚ x : ℝ) = archCoord (unitPart x) := by
  rw [distribHaarChar_eq_unitPart hprin, coe_distribHaarChar_unitPart hprod]

private theorem valued_natCast_eq_idealBound {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = idealBound (𝓞 ℚ) (Ideal.span {(n : 𝓞 ℚ)}) v := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have hn' : (n : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg hn', idealBound_of_ne_bot hN]

private theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (d : ℕ) :
    Valued.v ((d : ℕ) : v.adicCompletion ℚ) ≤ 1 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((d : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (d : 𝓞 ℚ) from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

private theorem natCast_level_eq (n : ℕ) (P : Nat.Primes) :
    ((n : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
      = (((P : ℕ) ^ n.factorization (P : ℕ) : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
        * ((n / (P : ℕ) ^ n.factorization (P : ℕ) : ℕ)
          : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) := by
  rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self n (P : ℕ)]

private theorem valued_ordCompl_eq_one {n : ℕ} (hn : n ≠ 0) (P : Nat.Primes) :
    Valued.v ((n / (P : ℕ) ^ n.factorization (P : ℕ) : ℕ)
      : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) = 1 := by
  rw [← map_natCast (algebraMap ℚ (((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)),
    valued_algebraMap_rat]
  exact valuation_natCast_of_not_dvd _
    (by rw [natGenerator_primesEquiv_symm]; exact Nat.not_dvd_ordCompl P.2 hn)

private theorem toZModPow_unitPadicAt (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ) (P : Nat.Primes)
    [Fact (P : ℕ).Prime] (hPmem : (P : ℕ) ∈ n.primeFactors) :
    PadicInt.toZModPow (n.factorization (P : ℕ)) (unitPadicAt (P : ℕ) y)
      = (((unitResidue n y).val : ℕ) : ZMod ((P : ℕ) ^ n.factorization (P : ℕ))) := by
  have h1 : ZMod.equivPi n (NeZero.ne n) ((((unitResidue n y).val : ℕ) : ZMod n))
      = unitResidues n y := by
    rw [ZMod.natCast_zmod_val, equivPi_unitResidue]
  rw [map_natCast] at h1
  have h2 := congrFun h1 ⟨(P : ℕ), hPmem⟩
  rw [Pi.natCast_apply] at h2
  exact h2.symm

private theorem exists_unitPadicAt_sub_eq (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ) (P : Nat.Primes)
    [Fact (P : ℕ).Prime] (hPmem : (P : ℕ) ∈ n.primeFactors) :
    ∃ c : ℤ_[(P : ℕ)], unitPadicAt (P : ℕ) y - (((unitResidue n y).val : ℕ) : ℤ_[(P : ℕ)])
      = (((P : ℕ) ^ n.factorization (P : ℕ) : ℕ) : ℤ_[(P : ℕ)]) * c := by
  have hker : unitPadicAt (P : ℕ) y - (((unitResidue n y).val : ℕ) : ℤ_[(P : ℕ)])
      ∈ RingHom.ker (PadicInt.toZModPow (p := (P : ℕ)) (n.factorization (P : ℕ))) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, toZModPow_unitPadicAt n y P hPmem, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨c, hc⟩ := hker
  exact ⟨c, by rw [Nat.cast_pow]; exact hc⟩

private noncomputable abbrev padicToCompletion (P : Nat.Primes) [Fact (P : ℕ).Prime] :
    ℤ_[(P : ℕ)] →+* ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ :=
  (((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletionIntegers ℚ).subtype.comp
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P).toAlgEquiv.toRingEquiv.toRingHom

private theorem padicToCompletion_unitPadicAt (y : (𝔸ℚ)ˣ) (P : Nat.Primes) :
    haveI : Fact (P : ℕ).Prime := ⟨P.2⟩
    padicToCompletion P (unitPadicAt (P : ℕ) y) = unitAt ((primesEquiv (R := 𝓞 ℚ)).symm P) y := by
  unfold unitPadicAt
  show (((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P)
      ((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P).symm
        (unitIntAt ((primesEquiv (R := 𝓞 ℚ)).symm P) y))
      : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletionIntegers ℚ)
      : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) = _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  exact coe_unitIntAt _ y

private theorem exists_unitAt_sub_residue_eq (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ) (P : Nat.Primes)
    (hPmem : (P : ℕ) ∈ n.primeFactors) :
    ∃ z : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletionIntegers ℚ,
      unitAt ((primesEquiv (R := 𝓞 ℚ)).symm P) y
          - (((unitResidue n y).val : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
        = (((P : ℕ) ^ n.factorization (P : ℕ) : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)
            * (z : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) := by
  haveI : Fact (P : ℕ).Prime := ⟨P.2⟩
  obtain ⟨c, hc⟩ := exists_unitPadicAt_sub_eq n y P hPmem
  refine ⟨PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) P c, ?_⟩
  have h1 := congrArg (padicToCompletion P) hc
  rw [map_sub (padicToCompletion P), map_natCast (padicToCompletion P), map_mul (padicToCompletion P),
    map_natCast (padicToCompletion P), padicToCompletion_unitPadicAt y P] at h1
  exact h1

private theorem valued_unitAt_sub_residue_le (n : ℕ) [NeZero n] (y : (𝔸ℚ)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (unitAt v y - (((unitResidue n y).val : ℕ) : v.adicCompletion ℚ))
      ≤ idealBound (𝓞 ℚ) (Ideal.span {(n : 𝓞 ℚ)}) v := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [← valued_natCast_eq_idealBound hn v]
  obtain ⟨P, rfl⟩ : ∃ P : Nat.Primes, (primesEquiv (R := 𝓞 ℚ)).symm P = v :=
    ⟨primesEquiv v, (primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v⟩
  by_cases hdvd : (P : ℕ) ∣ n
  · obtain ⟨z, hz⟩ := exists_unitAt_sub_residue_eq n y P (Nat.mem_primeFactors.mpr ⟨P.2, hdvd, hn⟩)
    have hz1 : Valued.v (z : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ _).mp z.2
    rw [hz, Valued.v.map_mul, natCast_level_eq n P, Valued.v.map_mul, valued_ordCompl_eq_one hn P,
      mul_one]
    exact mul_le_of_le_one_right' hz1
  · have h1 : Valued.v ((n : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ) = 1 := by
      rw [← map_natCast (algebraMap ℚ (((primesEquiv (R := 𝓞 ℚ)).symm P).adicCompletion ℚ)),
        valued_algebraMap_rat]
      exact valuation_natCast_of_not_dvd _ (by rw [natGenerator_primesEquiv_symm]; exact hdvd)
    rw [h1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le (valued_unitAt _ y).le (valued_natCast_le_one _ _))

private theorem snd_unitPart_sub_residue_mem_idealBall (n : ℕ) [NeZero n] (x : (𝔸ℚ)ˣ) :
    ((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (((unitResidue n x).val : ℕ) : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  intro v
  rw [coe_sub_apply, snd_unitPart,
    show (algebraMap ℚ 𝔸ℚf (((unitResidue n x).val : ℕ) : ℚ)) v
      = algebraMap ℚ (v.adicCompletion ℚ) (((unitResidue n x).val : ℕ) : ℚ) from rfl,
    map_natCast, ← unitResidue_unitPart n x]
  exact valued_unitAt_sub_residue_le n (unitPart x) v

private theorem algebraMap_natCast_mem_idealBall {n : ℕ} (hn : n ≠ 0) :
    algebraMap ℚ 𝔸ℚf ((n : ℕ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  intro v
  rw [show (algebraMap ℚ 𝔸ℚf ((n : ℕ) : ℚ)) v = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) from rfl,
    map_natCast, valued_natCast_eq_idealBound hn v]

private theorem neg_mem_idealBall {N : Ideal (𝓞 ℚ)} {z : 𝔸ℚf} (hz : z ∈ idealBall (𝓞 ℚ) ℚ N) :
    -z ∈ idealBall (𝓞 ℚ) ℚ N := fun v => by
  rw [coe_neg_apply, Valuation.map_neg]; exact hz v

private theorem centralScalar_comm (y : (𝔸ℚ)ˣ) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    centralScalar (𝓞 ℚ) ℚ y * X = X * centralScalar (𝓞 ℚ) ℚ y := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (y : 𝔸ℚ) * (X : Matrix (Fin 2) (Fin 2) 𝔸ℚ)
    = (X : Matrix (Fin 2) (Fin 2) 𝔸ℚ) * Matrix.scalar (Fin 2) (y : 𝔸ℚ)
  exact (Matrix.scalar_commute (y : 𝔸ℚ) (fun r => Commute.all _ r) _).eq

private theorem centralScalar_principal (q : ℚˣ) :
    centralScalar (𝓞 ℚ) ℚ (principal q)
      = globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (algebraMap ℚ 𝔸ℚ (q : ℚ))
    = (Matrix.scalar (Fin 2) (q : ℚ)).map (algebraMap ℚ 𝔸ℚ)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

private theorem glFin_centralScalar_val (y : (𝔸ℚ)ˣ) :
    ((glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ y) : GL (Fin 2) 𝔸ℚf) : Matrix (Fin 2) (Fin 2) 𝔸ℚf)
      = Matrix.diagonal (fun _ => ((y : 𝔸ℚ)).2) := by
  ext i j
  rw [glFin_apply, centralScalar_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> rfl

private theorem glFin_mapGL_mul_centralScalar_apply (ε : SL(2, ℤ)) (y : (𝔸ℚ)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * centralScalar (𝓞 ℚ) ℚ y)
        : GL (Fin 2) 𝔸ℚf) : Matrix (Fin 2) (Fin 2) 𝔸ℚf) i j
      = algebraMap ℚ 𝔸ℚf ((ε i j : ℤ) : ℚ) * ((y : 𝔸ℚ)).2 := by
  rw [map_mul, Units.val_mul, glFin_centralScalar_val, Matrix.mul_diagonal,
    glFin_globalPoints_apply]
  congr 1

private theorem isLevelOneMatrix_mapGL_mul_centralScalar {n : ℕ} (ε : SL(2, ℤ)) (y : (𝔸ℚ)ˣ)
    (hint : ((y : 𝔸ℚ)).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hc : algebraMap ℚ 𝔸ℚf ((ε 1 0 : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}))
    (hd : algebraMap ℚ 𝔸ℚf ((ε 1 1 : ℤ) : ℚ) * ((y : 𝔸ℚ)).2 - 1
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * centralScalar (𝓞 ℚ) ℚ y)
        : GL (Fin 2) 𝔸ℚf) : Matrix (Fin 2) (Fin 2) 𝔸ℚf) := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [glFin_mapGL_mul_centralScalar_apply]
    exact mul_mem_integralFiniteAdeles (intCast_mem_integralFiniteAdeles _) hint
  · rw [glFin_mapGL_mul_centralScalar_apply]
    exact mul_mem_idealBall_right hc hint
  · rw [glFin_mapGL_mul_centralScalar_apply]
    exact hd

private def twistMat {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) : SL(2, ℤ) :=
  ⟨!![d, m; (n : ℤ), a], by rw [Matrix.det_fin_two_of]; exact hdet⟩

private theorem twistMat_apply_10 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    twistMat (n := n) d m a hdet 1 0 = (n : ℤ) := rfl

private theorem twistMat_apply_11 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    twistMat (n := n) d m a hdet 1 1 = a := rfl

private theorem twistMat_inv_apply_10 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    (twistMat (n := n) d m a hdet)⁻¹ 1 0 = -(n : ℤ) := by
  simp [twistMat, Matrix.SpecialLinearGroup.SL2_inv_expl]

private theorem twistMat_inv_apply_11 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    (twistMat (n := n) d m a hdet)⁻¹ 1 1 = d := by
  simp [twistMat, Matrix.SpecialLinearGroup.SL2_inv_expl]

private theorem twistMat_mem_Gamma0 {n : ℕ} (d m a : ℤ) (hdet : d * a - m * n = 1) :
    twistMat (n := n) d m a hdet ∈ Gamma0 n := by
  rw [Gamma0_mem, twistMat_apply_10, Int.cast_natCast, ZMod.natCast_self]

private theorem glFin_twist_mem_finiteLevelOne (n : ℕ) [NeZero n] (x : (𝔸ℚ)ˣ) (m a : ℤ)
    (hdet : ((unitResidue n x).val : ℤ) * a - m * n = 1) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (Matrix.SpecialLinearGroup.mapGL ℚ (twistMat (n := n) ((unitResidue n x).val : ℤ) m a hdet))
      * centralScalar (𝓞 ℚ) ℚ (unitPart x))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  have hn : n ≠ 0 := NeZero.ne n
  set d : ℤ := ((unitResidue n x).val : ℤ) with hd_def
  have hball : ((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (d : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [hd_def, Int.cast_natCast]
    exact snd_unitPart_sub_residue_mem_idealBall n x
  have hnball : algebraMap ℚ 𝔸ℚf (((n : ℕ) : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [Int.cast_natCast]; exact algebraMap_natCast_mem_idealBall hn
  rw [mem_finiteLevelOne_iff]
  refine ⟨?_, ?_⟩
  ·
    refine isLevelOneMatrix_mapGL_mul_centralScalar _ _ (snd_unitPart_mem_integral x) ?_ ?_
    · rw [twistMat_apply_10]; exact hnball
    · rw [twistMat_apply_11]

      have hkey : algebraMap ℚ 𝔸ℚf (a : ℚ) * ((unitPart x : 𝔸ℚ)).2 - 1
          = algebraMap ℚ 𝔸ℚf (a : ℚ) * (((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (d : ℚ))
            + algebraMap ℚ 𝔸ℚf (m : ℚ) * algebraMap ℚ 𝔸ℚf (((n : ℕ) : ℤ) : ℚ) := by
        have hmn : a * d - 1 = m * n := by linear_combination hdet
        have h2 : algebraMap ℚ 𝔸ℚf (m : ℚ) * algebraMap ℚ 𝔸ℚf (((n : ℕ) : ℤ) : ℚ)
            = algebraMap ℚ 𝔸ℚf (a : ℚ) * algebraMap ℚ 𝔸ℚf (d : ℚ) - 1 := by
          rw [← map_mul, ← map_mul, ← map_one (algebraMap ℚ 𝔸ℚf), ← map_sub, ← Int.cast_mul,
            ← Int.cast_mul, ← Int.cast_one, ← Int.cast_sub, hmn]
        rw [h2]; ring
      rw [hkey]
      exact add_mem_idealBall (mul_mem_idealBall_left (intCast_mem_integralFiniteAdeles _) hball)
        (mul_mem_idealBall_left (intCast_mem_integralFiniteAdeles _) hnball)
  ·
    rw [← map_inv, _root_.mul_inv_rev, ← map_inv, ← map_inv, ← map_inv, centralScalar_comm]
    refine isLevelOneMatrix_mapGL_mul_centralScalar _ _ (snd_inv_unitPart_mem_integral x) ?_ ?_
    · rw [twistMat_inv_apply_10, Int.cast_neg, map_neg]; exact neg_mem_idealBall hnball
    · rw [twistMat_inv_apply_11]

      have hkey : algebraMap ℚ 𝔸ℚf (d : ℚ) * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 - 1
          = -(((unitPart x : 𝔸ℚ)).2 - algebraMap ℚ 𝔸ℚf (d : ℚ)) * (((unitPart x)⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 := by
        rw [neg_sub, sub_mul, snd_unitPart_mul_snd_inv]
      rw [hkey]
      exact mul_mem_idealBall_right (neg_mem_idealBall hball) (snd_inv_unitPart_mem_integral x)

private theorem exists_twist (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (x : (𝔸ℚ)ˣ) :
    ∃ ε : SL(2, ℤ), ε ∈ Gamma0 n
      ∧ χ ((ε 1 1 : ℤ) : ZMod n) = (χ (unitResidue n x))⁻¹
      ∧ glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)
          * centralScalar (𝓞 ℚ) ℚ (unitPart x))
        ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
  have hru : IsUnit (unitResidue n x) := (Group.isUnit x).map (unitResidue n)

  have hmul : (((unitResidue n x).val : ℕ) : ZMod n) * (((unitResidue n x)⁻¹.val : ℕ) : ZMod n) = 1 := by
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact ZMod.mul_inv_of_unit _ hru
  have hdvd : ((n : ℕ) : ℤ) ∣ ((unitResidue n x).val : ℤ) * ((unitResidue n x)⁻¹.val : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hmul, sub_self]
  obtain ⟨m, hm⟩ := hdvd
  have hdet : ((unitResidue n x).val : ℤ) * ((unitResidue n x)⁻¹.val : ℤ) - m * n = 1 := by
    linear_combination hm
  refine ⟨twistMat (n := n) _ m _ hdet, twistMat_mem_Gamma0 _ _ _ _, ?_,
    glFin_twist_mem_finiteLevelOne n x m _ hdet⟩
  rw [twistMat_apply_11, Int.cast_natCast, ZMod.natCast_zmod_val]
  have h1 : χ (unitResidue n x)⁻¹ * χ (unitResidue n x) = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit _ hru, map_one]
  exact eq_inv_of_mul_eq_one_left h1

private theorem det_coe_SL (ε : SL(2, ℤ)) : ((ε : GL (Fin 2) ℝ)).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.SpecialLinearGroup.det_coe _

private theorem ratArch_centralScalar_val (y : (𝔸ℚ)ˣ) :
    ((ratArch (centralScalar (𝓞 ℚ) ℚ y) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = archCoord y • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply]
  show InfinitePlace.Completion.ringEquivRealOfIsReal
      (isReal_rat_infinitePlace default)
      ((((centralScalar (𝓞 ℚ) ℚ y : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) 𝔸ℚ) i j).1 default) = _
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl, smul_eq_mul, mul_one,
      show (default : InfinitePlace ℚ) = Rat.infinitePlace from Subsingleton.elim _ _]
    rfl
  · rw [centralScalar_apply_ne y h, if_neg h, smul_zero]
    exact map_zero _

private theorem det_ratArch_centralScalar (y : (𝔸ℚ)ˣ) :
    (ratArch (centralScalar (𝓞 ℚ) ℚ y)).det.val = archCoord y * archCoord y := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, ratArch_centralScalar_val, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin, sq]

private theorem weightOneArchLift_mul_ratArch_centralScalar (f : ℍ → ℂ) (H : GL (Fin 2) ℝ)
    (x : (𝔸ℚ)ˣ) :
    weightOneArchLift f (H * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)))
      = ((archCoord (unitPart x) : ℝ) : ℂ) * weightOneArchLift f H := by
  have hcomm : H * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x))
      = ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)) * H := by
    apply Units.ext
    show (H : Matrix (Fin 2) (Fin 2) ℝ) * (ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)) : Matrix (Fin 2) (Fin 2) ℝ)
      = (ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x)) : Matrix (Fin 2) (Fin 2) ℝ) * (H : Matrix (Fin 2) (Fin 2) ℝ)
    rw [ratArch_centralScalar_val, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hcomm]
  exact R1.weightOneArchLift_scalar_mul f _ H _ (archCoord_unitPart_pos x) (ratArch_centralScalar_val _)

private theorem weightOneArchLift_gamma0_mul {n : ℕ} (f : ℍ → ℂ) (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 n) (M : GL (Fin 2) ℝ) (hM : 0 < M.det.val) :
    weightOneArchLift f ((γ : GL (Fin 2) ℝ) * M)
      = χ ((γ 1 1 : ℤ) : ZMod n) * weightOneArchLift f M := by
  have hσ : σ M (χ ((γ 1 1 : ℤ) : ZMod n)) = χ ((γ 1 1 : ℤ) : ZMod n) := by
    rw [σ, if_pos hM]
    rfl
  rw [R1.weightOneArchLift_def, R1.weightOneArchLift_def, SlashAction.slash_mul, hχ γ hγ,
    ModularForm.smul_slash, map_mul, Units.val_mul, det_coe_SL, one_mul, Pi.smul_apply, hσ,
    smul_eq_mul]
  ring

private theorem weightOneLift_centralScalar_unitPart_mul {n : ℕ} [NeZero n] (hn : n ≠ 0)
    (f : ℍ → ℂ) (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (x : (𝔸ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (unitPart x) * g)
      = (χ (unitResidue n x))⁻¹ * ((archCoord (unitPart x) : ℝ) : ℂ)
          * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨ε, hε, hχε, hkε⟩ := exists_twist n χ x
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  have hglArch_u : glArch (𝓞 ℚ) ℚ u = 1 := ((R7.mem_U_iff _ u).mp hu).2
  have hfin_u : glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) :=
    ((R7.mem_U_iff _ u).mp hu).1

  have hprod : centralScalar (𝓞 ℚ) ℚ (unitPart x) * g
      = globalPoints (𝓞 ℚ) ℚ (γ * (Matrix.SpecialLinearGroup.mapGL ℚ ε)⁻¹)
        * (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
            * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u) := by
    rw [hg, map_mul, map_inv, ← mul_assoc, centralScalar_comm]
    group

  have hkf : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
        * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u)
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [map_mul, map_mul, map_mul, hfin, mul_one, ← map_mul]
    exact mul_mem hkε hfin_u

  have hratk : ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
        * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u)
      = (ε : GL (Fin 2) ℝ) * (ratArch h * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x))) := by
    rw [ratArch_mul, ratArch_mul, ratArch_mul, ratArch_globalPoints_mapGL,
      ratArch_eq_one_of_glArch_eq_one hglArch_u, mul_one, mul_assoc]
  have hdetH : 0 < (ratArch h).det.val := by
    rw [← R4a.ratArchGL2_eq_ratArch]
    exact hpos
  have hdetM : 0 < (ratArch h * ratArch (centralScalar (𝓞 ℚ) ℚ (unitPart x))).det.val := by
    rw [map_mul, Units.val_mul, det_ratArch_centralScalar]
    exact mul_pos hdetH (mul_pos (archCoord_unitPart_pos x) (archCoord_unitPart_pos x))
  have hdetk : 0 < (ratArch 1 * ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε) * h
        * centralScalar (𝓞 ℚ) ℚ (unitPart x) * u)).det.val := by
    rw [ratArch_one, one_mul, hratk, map_mul, Units.val_mul, det_coe_SL, one_mul]
    exact hdetM
  have hR7 := R7.weightOneLift_mul_eq hn f hf
    (g₀ := globalPoints (𝓞 ℚ) ℚ (γ * (Matrix.SpecialLinearGroup.mapGL ℚ ε)⁻¹))
    (γ₀ := γ * (Matrix.SpecialLinearGroup.mapGL ℚ ε)⁻¹)
    (one_mem _) (map_one (glFin (𝓞 ℚ) ℚ)) (by rw [mul_one, mul_one]) _ hkf hdetk
  rw [hprod, hR7, ratArch_one, one_mul, hratk, weightOneArchLift_gamma0_mul f χ hχ ε hε _ hdetM,
    weightOneArchLift_mul_ratArch_centralScalar, hχε,
    R4a.weightOneLift_eq hn f hf g γ h u hu hfin hpos hg, R4a.ratArchGL2_eq_ratArch, mul_assoc]

private theorem weightOneLift_centralScalar_mul_eq {n : ℕ} [NeZero n] (hn : n ≠ 0)
    (f : ℍ → ℂ) (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (x : (𝔸ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hprin : ∀ q : ℚˣ,
      MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) = 1)
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ x * g)
      = ((DirichletCharacter.dirichletIdeleChar χ x : ℂˣ) : ℂ)
          * ((MeasureTheory.distribHaarChar 𝔸ℚ x : ℝ) : ℂ)
          * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  conv_lhs => rw [← principal_mul_unitPart x, map_mul, mul_assoc, centralScalar_principal,
    R4a.weightOneLift_globalPoints_mul hn f hf]
  rw [weightOneLift_centralScalar_unitPart_mul hn f hf χ hχ x g,
    DirichletCharacter.coe_dirichletIdeleChar_apply, coe_distribHaarChar_eq_archCoord hprin hprod]

end

end P2GProbe.C1

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne in
open scoped ModularForm MatrixGroups in
theorem solution
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f) :
    ∀ (z : (productionPinsCompact ℚ).Z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g)
        = ((((DirichletCharacter.dirichletIdeleChar χ *
            (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
              (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          (productionPinsCompact ℚ).Z.subtype) z : ℂˣ) : ℂ) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hprin := fun q : ℚˣ => @NumberField.AdeleRing.distribHaarChar_algebraMap ℚ _ _
    (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (NumberField.RingOfIntegers ℚ) ℚ) q
  have hprod := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ
  intro z g
  exact P2GProbe.C1.weightOneLift_centralScalar_mul_eq hn f hf χ hχ
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) g hprin hprod

end S_LanglandsTunnell_weightOneLift_centralScalar_mul
end P2MW
export P2MW.S_LanglandsTunnell_weightOneLift_centralScalar_mul (solution)
