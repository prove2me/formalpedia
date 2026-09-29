-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.dualTranslate_finWhittaker_local_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/094193a5-af73-5dae-8b34-b1a039dc55fb

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_dualTranslate_finWhittaker_local_relations
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse

section Ws23FactPhiDualSupply

open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

noncomputable section

namespace Ws23FactPhiDual
open Matrix MeasureTheory NumberField.InfinitePlace.Completion

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev w0 : InfinitePlace ℚ := default
theorem hw0 : (w0).IsReal := IsTotallyReal.isReal _
abbrev eR : (w0).Completion ≃+* ℝ := ringEquivRealOfIsReal hw0
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hw0

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = w0 := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ w0 ((glEquivOfRingEquiv (eR).symm M : GL (Fin 2) (w0).Completion) : Matrix _ _ _) i j w0 = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem iotaR_snd (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := rfl

abbrev fstM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev sndM (g : G2) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem fstM_mul (g h : G2) : fstM (g * h) = fstM g * fstM h := (RingHom.mapMatrix _).map_mul _ _
theorem sndM_mul (g h : G2) : sndM (g * h) = sndM g * sndM h := (RingHom.mapMatrix _).map_mul _ _

theorem eq_of_fstM_sndM {g h : G2} (h1 : fstM g = fstM h) (h2 : sndM g = sndM h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem fstM_eq_one_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : fstM g = 1 := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) hg

theorem mem_of_fstM_eq_one {g : G2} (hg : fstM g = 1) : g ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact Units.ext hg

theorem sndM_iotaR (M : GL (Fin 2) ℝ) : sndM (ιR M) = 1 := Matrix.ext fun i j => iotaR_snd M i j

theorem iotaR_mul_comm {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) : ιR M * g = g * ιR M := by
  refine eq_of_fstM_sndM ?_ ?_
  · rw [fstM_mul, fstM_mul, fstM_eq_one_of_mem hg, mul_one, one_mul]
  · rw [sndM_mul, sndM_mul, sndM_iotaR, mul_one, one_mul]

theorem ratArchGL2_apply (g : G2) (i j : Fin 2) :
    ((ratArchGL2 g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = eR (((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) := rfl

theorem ratArchGL2_mul (g h : G2) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_inv (g : G2) : ratArchGL2 g⁻¹ = (ratArchGL2 g)⁻¹ := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_inv, map_inv, map_inv]

theorem ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem ratArchGL2_iotaR (M : GL (Fin 2) ℝ) : ratArchGL2 (ιR M) = M := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratArchGL2_apply, iotaR_fst]
  exact (eR).apply_symm_apply _

theorem coe_finFactor (g : G2) : (RSCarrier.finFactor g : G2) = (ιR (ratArchGL2 g))⁻¹ * g := rfl

end Ws23FactPhiDual

end

end Ws23FactPhiDualSupply

section Ws23HeckeLocalDualSupply

open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

noncomputable section

namespace Ws23HeckeLocalDual

open Matrix Ws23FactPhiDual NumberField.AdelicVolume UnramifiedWhittaker

local notation "T" => transposeInvN (Fin 2)

theorem finFactor_mul_of_mem (g : G2) {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * x) = ⟨(RSCarrier.finFactor g : G2) * x, mul_mem (RSCarrier.finFactor g).2 hx⟩ := by
  apply Subtype.ext
  show (ιR (ratArchGL2 (g * x)))⁻¹ * (g * x) = (ιR (ratArchGL2 g))⁻¹ * g * x
  rw [ratArchGL2_mul, ratArchGL2_of_mem hx, mul_one, mul_assoc]

theorem finFactor_mul_of_mem_left (g : G2) {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (x * g) = ⟨x * (RSCarrier.finFactor g : G2), mul_mem hx (RSCarrier.finFactor g).2⟩ := by
  apply Subtype.ext
  show (ιR (ratArchGL2 (x * g)))⁻¹ * (x * g) = x * ((ιR (ratArchGL2 g))⁻¹ * g)
  rw [ratArchGL2_mul, ratArchGL2_of_mem hx, one_mul, ← mul_assoc, ← mul_assoc, ← map_inv, iotaR_mul_comm hx]

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

abbrev Kp : Type := p.adicCompletion ℚ
abbrev Op : Type := p.adicCompletionIntegers ℚ

theorem placeEmbed_eq (x : GL (Fin 2) (Kp p)) :
    placeEmbed ℚ p x = AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x) := rfl

theorem placeEmbed_mem_fin (x : GL (Fin 2) (Kp p)) : placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff, placeEmbed_eq, AdelicDock.glArch_finEmbed]

theorem localAt_placeEmbed (x : GL (Fin 2) (Kp p)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ
    (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

abbrev archM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev finM (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
    ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸))

theorem archM_mul (g h : G2) : archM (g * h) = archM g * archM h := (RingHom.mapMatrix _).map_mul _ _
theorem finM_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g h : G2) : finM w (g * h) = finM w g * finM w h := by
  show (RingHom.mapMatrix _) ((RingHom.mapMatrix _) (_ * _)) = _
  rw [map_mul, map_mul]

theorem eq_of_components {g h : G2} (ha : archM g = archM h) (hf : ∀ w, finM w g = finM w h) : g = h :=
  Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ha
    (AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ hf))

theorem archM_placeEmbed (x : GL (Fin 2) (Kp p)) : archM (placeEmbed ℚ p x) = 1 := by
  show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix _ = 1
  rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat]

theorem finM_placeEmbed_self (x : GL (Fin 2) (Kp p)) : finM p (placeEmbed ℚ p x) = x := by
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _) = _
  rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed,
    AdelicDock.mapMatrix_localMat_self]

theorem finM_placeEmbed_of_ne (x : GL (Fin 2) (Kp p)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ p) :
    finM w (placeEmbed ℚ p x) = 1 := by
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _) = _
  rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed,
    AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw]

theorem finM_self_eq_localAt (g : G2) : finM p g = ((localAt ℚ p g : GL (Fin 2) (Kp p)) : Matrix _ _ _) := rfl

theorem mapMatrix_T {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 2) A) :
    f.mapMatrix ((T g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      ((T (Matrix.GeneralLinearGroup.map f g) : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
  rw [coe_transposeInvN, coe_transposeInvN, ← map_inv]
  ext i j
  rfl

theorem archM_T (g : G2) : archM (T g) =
    ((T (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) g) : GL (Fin 2) _) : Matrix _ _ _) :=
  mapMatrix_T _ g

theorem finM_T (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) : finM w (T g) =
    ((T (Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) g) :
      GL (Fin 2) _) : Matrix _ _ _) := by
  rw [← mapMatrix_T]
  rfl

theorem T_one' {A : Type*} [CommRing A] : T (1 : GL (Fin 2) A) = 1 :=
  Units.ext (by rw [coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one])

theorem map_placeEmbed_arch (x : GL (Fin 2) (Kp p)) :
    Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (placeEmbed ℚ p x) = 1 :=
  Units.ext (archM_placeEmbed p x)

theorem map_placeEmbed_self (x : GL (Fin 2) (Kp p)) :
    Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (placeEmbed ℚ p x) = x :=
  Units.ext (by show finM p (placeEmbed ℚ p x) = _; exact finM_placeEmbed_self p x)

theorem map_placeEmbed_of_ne (x : GL (Fin 2) (Kp p)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ p) :
    Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (placeEmbed ℚ p x) = 1 :=
  Units.ext (by show finM w (placeEmbed ℚ p x) = _; rw [finM_placeEmbed_of_ne p x hw, Units.val_one])

theorem T_placeEmbed (x : GL (Fin 2) (Kp p)) : T (placeEmbed ℚ p x) = placeEmbed ℚ p (T x) := by
  refine eq_of_components ?_ (fun w => ?_)
  · rw [archM_T, map_placeEmbed_arch, T_one', archM_placeEmbed, Units.val_one]
  · by_cases hw : w = p
    · subst hw
      rw [finM_T, map_placeEmbed_self, finM_placeEmbed_self]
    · rw [finM_T, map_placeEmbed_of_ne _ _ hw, T_one', finM_placeEmbed_of_ne _ _ hw, Units.val_one]

theorem mul_placeEmbed_comm {k : G2} (hk : localAt ℚ p k = 1) (x : GL (Fin 2) (Kp p)) :
    k * placeEmbed ℚ p x = placeEmbed ℚ p x * k := by
  refine eq_of_components ?_ (fun w => ?_)
  · rw [archM_mul, archM_mul, archM_placeEmbed, mul_one, one_mul]
  · by_cases hw : w = p
    · subst hw
      rw [finM_mul, finM_mul, finM_placeEmbed_self, finM_self_eq_localAt, hk, Units.val_one]
      simp
    · rw [finM_mul, finM_mul, finM_placeEmbed_of_ne _ _ hw, mul_one, one_mul]

abbrev ratLoc (γ : GL (Fin 2) ℚ) : GL (Fin 2) (Kp p) := Matrix.GeneralLinearGroup.map (algebraMap ℚ (Kp p)) γ

theorem finM_globalPoints (γ : GL (Fin 2) ℚ) : finM p (globalPoints (𝓞 ℚ) ℚ γ) = (ratLoc p γ : Matrix _ _ _) := rfl

theorem globalPoints_mul_placeEmbed (γ : GL (Fin 2) ℚ) (x : GL (Fin 2) (Kp p)) :
    globalPoints (𝓞 ℚ) ℚ γ * placeEmbed ℚ p x =
      placeEmbed ℚ p (ratLoc p γ * x * (ratLoc p γ)⁻¹) * globalPoints (𝓞 ℚ) ℚ γ := by
  refine eq_of_components ?_ (fun w => ?_)
  · rw [archM_mul, archM_mul, archM_placeEmbed, archM_placeEmbed, mul_one, one_mul]
  · by_cases hw : w = p
    · subst hw
      rw [finM_mul, finM_mul, finM_placeEmbed_self, finM_placeEmbed_self, finM_globalPoints,
        ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    · rw [finM_mul, finM_mul, finM_placeEmbed_of_ne _ _ hw, finM_placeEmbed_of_ne _ _ hw, mul_one, one_mul]

theorem finIncl_fst (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : (AdelicLevel.finIncl (𝓞 ℚ) ℚ y).1 = 1 := rfl
theorem finIncl_snd (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : (AdelicLevel.finIncl (𝓞 ℚ) ℚ y).2 = y := rfl

theorem det_placeEmbed (x : GL (Fin 2) (Kp p)) :
    Matrix.GeneralLinearGroup.det (placeEmbed ℚ p x) =
      Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (Matrix.GeneralLinearGroup.det x)) := by
  have hA := RingHom.map_det (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) ((placeEmbed ℚ p x : G2) : Matrix (Fin 2) (Fin 2) 𝔸)
  have hF := RingHom.map_det (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) ((placeEmbed ℚ p x : G2) : Matrix (Fin 2) (Fin 2) 𝔸)
  rw [AdelicLevel.adeleArch_apply] at hA
  rw [AdelicLevel.adeleFin_apply] at hF
  refine Units.ext (Prod.ext ?_ ?_)
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, finIncl_fst, hA]
    show (archM (placeEmbed ℚ p x)).det = 1
    rw [archM_placeEmbed, Matrix.det_one]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, finIncl_snd, hF]
    refine Subtype.ext (funext fun w => ?_)
    have hw' := RingHom.map_det (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w)
      ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix ((placeEmbed ℚ p x : G2) : Matrix (Fin 2) (Fin 2) 𝔸))
    rw [AdelicLevel.finAdeleEval_apply] at hw'
    show (((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix ((placeEmbed ℚ p x : G2) : Matrix (Fin 2) (Fin 2) 𝔸)).det) w = _
    rw [hw']
    show (finM w (placeEmbed ℚ p x)).det = _
    by_cases hw : w = p
    · subst hw
      rw [finM_placeEmbed_self, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact (AdelicLevel.localUnit_apply_self (𝓞 ℚ) ℚ _ _).symm
    · rw [finM_placeEmbed_of_ne _ _ hw, Matrix.det_one]
      exact (AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ _ _ hw).symm

end Place

section Local

variable {p : HeightOneSpectrum (𝓞 ℚ)}
variable (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])

theorem T_eq_of_transpose_mul {A : Type*} [CommRing A] (m n : GL (Fin 2) A)
    (h : ((n : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ * (m : Matrix (Fin 2) (Fin 2) A) = 1) : T m = n := by
  have hinv : ((m⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = ((n : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv h
  refine Units.ext ?_
  rw [coe_transposeInvN, hinv, Matrix.transpose_transpose]

theorem mem_K_of_entries {x : GL (Fin 2) (Kp p)}
    (h1 : ∀ i j, (x : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ)
    (h2 : ∀ i j, ((x⁻¹ : GL (Fin 2) (Kp p)) : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ) :
    x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (Kp p), (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨hm, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (hm 1 1) (one_mem _))
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨key _ h1, key _ h2⟩

theorem entries_of_mem_K {x : GL (Fin 2) (Kp p)} (hx : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    (∀ i j, (x : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ) ∧
    (∀ i j, ((x⁻¹ : GL (Fin 2) (Kp p)) : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ) := by
  rw [AdelicDock.mem_localLevelOne_iff] at hx
  exact ⟨hx.1.integral, hx.2.integral⟩

theorem T_mem_K {x : GL (Fin 2) (Kp p)} (hx : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    T x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  obtain ⟨h1, h2⟩ := entries_of_mem_K hx
  refine mem_K_of_entries (fun i j => ?_) (fun i j => ?_)
  · rw [coe_transposeInvN, Matrix.transpose_apply]; exact h2 j i
  · rw [coe_inv_transposeInvN, Matrix.transpose_apply]; exact h1 j i

def gl2 (a b c d a' b' c' d' : Kp p) (h : !![a, b; c, d] * !![a', b'; c', d'] = 1)
    (h' : !![a', b'; c', d'] * !![a, b; c, d] = 1) : GL (Fin 2) (Kp p) :=
  ⟨!![a, b; c, d], !![a', b'; c', d'], h, h'⟩

include hw₀ in

theorem ratLoc_w₀_val : ((ratLoc p w₀ : GL (Fin 2) (Kp p)) : Matrix (Fin 2) (Fin 2) (Kp p)) = !![0, 1; 1, 0] := by
  show (algebraMap ℚ (Kp p)).mapMatrix ((w₀ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
  rw [hw₀]
  ext i j; fin_cases i <;> fin_cases j <;> simp

include hw₀ in
theorem ratLoc_w₀_inv : (ratLoc p w₀)⁻¹ = ratLoc p w₀ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, ratLoc_w₀_val w₀ hw₀, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

include hw₀ in

theorem conj_T_unipotent (x : Kp p) :
    ratLoc p w₀ * T (unipotent x) * (ratLoc p w₀)⁻¹ = unipotent (-x) := by
  have hT : T (unipotent x) = Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; -x, 1]
      (by rw [Matrix.det_fin_two_of]; simp) := by
    refine T_eq_of_transpose_mul _ _ ?_
    show (!![(1 : Kp p), 0; -x, 1])ᵀ * !![1, x; 0, 1] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hT, ratLoc_w₀_inv w₀ hw₀]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ratLoc_w₀_val w₀ hw₀]
  show !![(0 : Kp p), 1; 1, 0] * !![1, 0; -x, 1] * !![0, 1; 1, 0] = !![1, -x; 0, 1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable (π : Kp p) (hπ : π ≠ 0)

def Lmat (β : Kp p) : GL (Fin 2) (Kp p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; -β, π] (by rw [Matrix.det_fin_two_of]; simpa using hπ)

def dπ : GL (Fin 2) (Kp p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![π, 0; 0, 1] (by rw [Matrix.det_fin_two_of]; simpa using hπ)

include hπ in
theorem scalarPi_mul_T_repSome (β : Kp p) : scalarPi π hπ * T (repSome π hπ β) = Lmat π hπ β := by
  have hT : T (repSome π hπ β) = Matrix.GeneralLinearGroup.mkOfDetNeZero !![π⁻¹, 0; -β * π⁻¹, 1]
      (by rw [Matrix.det_fin_two_of]; simp [hπ]) := by
    refine T_eq_of_transpose_mul _ _ ?_
    show (!![π⁻¹, 0; -β * π⁻¹, (1 : Kp p)])ᵀ * !![π, β; 0, 1] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ] <;> ring1
  rw [hT]
  refine Units.ext ?_
  show !![π, 0; 0, π] * !![π⁻¹, 0; -β * π⁻¹, (1 : Kp p)] = !![1, 0; -β, π]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ] <;> field_simp

include hπ in
theorem scalarPi_mul_T_repInf : scalarPi π hπ * T (repInf π hπ) = dπ π hπ := by
  have hT : T (repInf π hπ) = Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π⁻¹]
      (by rw [Matrix.det_fin_two_of]; simp [hπ]) := by
    refine T_eq_of_transpose_mul _ _ ?_
    show (!![(1 : Kp p), 0; 0, π⁻¹])ᵀ * !![1, 0; 0, π] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ]
  rw [hT]
  refine Units.ext ?_
  show !![π, 0; 0, π] * !![(1 : Kp p), 0; 0, π⁻¹] = !![π, 0; 0, 1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ]

include hπ in
theorem T_scalarPi : T (scalarPi π hπ) = (scalarPi π hπ)⁻¹ := by
  have hT : T (scalarPi π hπ) = Matrix.GeneralLinearGroup.mkOfDetNeZero !![π⁻¹, 0; 0, π⁻¹]
      (by rw [Matrix.det_fin_two_of]; simp [hπ]) := by
    refine T_eq_of_transpose_mul _ _ ?_
    show (!![π⁻¹, 0; 0, π⁻¹] : Matrix (Fin 2) (Fin 2) (Kp p))ᵀ * !![π, 0; 0, π] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ]
  rw [hT]
  refine (inv_eq_of_mul_eq_one_right (Units.ext ?_)).symm
  show !![π, 0; 0, π] * !![π⁻¹, 0; 0, π⁻¹] = (1 : Matrix (Fin 2) (Fin 2) (Kp p))
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ]

theorem det_unipotent (x : Kp p) : Matrix.GeneralLinearGroup.det (unipotent x) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det !![(1 : Kp p), x; 0, 1] = 1
  rw [Matrix.det_fin_two_of]; ring

theorem det_repSome (β : Kp p) : Matrix.GeneralLinearGroup.det (repSome π hπ β) = Units.mk0 π hπ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det !![π, β; 0, 1] = π
  rw [Matrix.det_fin_two_of]; ring

theorem det_repInf : Matrix.GeneralLinearGroup.det (repInf π hπ) = Units.mk0 π hπ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det !![1, 0; 0, π] = π
  rw [Matrix.det_fin_two_of]; ring

theorem det_scalarPi : Matrix.GeneralLinearGroup.det (scalarPi π hπ) = Units.mk0 π hπ * Units.mk0 π hπ := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det !![π, 0; 0, π] = π * π
  rw [Matrix.det_fin_two_of]; ring

theorem det_of_mem_K {κ : GL (Fin 2) (Kp p)} (hκ : κ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    Valued.v ((Matrix.GeneralLinearGroup.det κ : (Kp p)ˣ) : Kp p) = 1 := by
  obtain ⟨h1, h2⟩ := entries_of_mem_K hκ
  have hle : ∀ m : Matrix (Fin 2) (Fin 2) (Kp p), (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) →
      Valued.v m.det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      (sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0)))
  have hA := hle _ h1
  have hB := hle _ h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at hA hB
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at hB
  have hne : Valued.v ((Matrix.GeneralLinearGroup.det κ : (Kp p)ˣ) : Kp p) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Matrix.GeneralLinearGroup.det κ).ne_zero
  exact le_antisymm hA (by rwa [inv_le_one₀ (zero_lt_iff.2 hne)] at hB)

theorem unipotent_mem_K {c : Kp p} (hc : c ∈ p.adicCompletionIntegers ℚ) :
    unipotent c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have hinv : (unipotent c)⁻¹ = unipotent (-c) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    show !![(1 : Kp p), c; 0, 1] * !![1, -c; 0, 1] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_K_of_entries (fun i j => ?_) (fun i j => ?_)
  · show (!![(1 : Kp p), c; 0, 1]) i j ∈ _
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact hc
    · exact zero_mem _
    · exact one_mem _
  · rw [hinv]
    show (!![(1 : Kp p), -c; 0, 1]) i j ∈ _
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact neg_mem hc
    · exact zero_mem _
    · exact one_mem _

def lowU (c : Kp p) : GL (Fin 2) (Kp p) :=
  gl2 1 0 (-c) 1 1 0 c 1
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

theorem lowU_mem_K {c : Kp p} (hc : c ∈ p.adicCompletionIntegers ℚ) :
    lowU c ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  refine mem_K_of_entries (fun i j => ?_) (fun i j => ?_)
  · show (!![(1 : Kp p), 0; -c, 1]) i j ∈ _
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact neg_mem hc
    · exact one_mem _
  · show (!![(1 : Kp p), 0; c, 1]) i j ∈ _
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact hc
    · exact one_mem _

def cof (β β' c : Kp p) (hc : π * c = 1 + β * β') : GL (Fin 2) (Kp p) :=
  gl2 c (-β') (-β) π π β' β c
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hc)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hc)

theorem cof_mem_K {β β' c : Kp p} (hc : π * c = 1 + β * β') (hπi : π ∈ p.adicCompletionIntegers ℚ)
    (hβ : β ∈ p.adicCompletionIntegers ℚ) (hβ' : β' ∈ p.adicCompletionIntegers ℚ)
    (hci : c ∈ p.adicCompletionIntegers ℚ) : cof π β β' c hc ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  refine mem_K_of_entries (fun i j => ?_) (fun i j => ?_)
  · show (!![c, -β'; -β, π]) i j ∈ _
    fin_cases i <;> fin_cases j
    · exact hci
    · exact neg_mem hβ'
    · exact neg_mem hβ
    · exact hπi
  · show (!![π, β'; β, c]) i j ∈ _
    fin_cases i <;> fin_cases j
    · exact hπi
    · exact hβ'
    · exact hβ
    · exact hci

include hπ in

theorem dπ_eq (β₀ c₀ : Kp p) (h : β₀ = π * c₀) : dπ π hπ = repSome π hπ β₀ * unipotent (-c₀) := by
  refine Units.ext ?_
  show !![π, 0; 0, (1 : Kp p)] = !![π, β₀; 0, 1] * !![1, -c₀; 0, 1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

include hπ in

theorem Lmat_eq_repInf (β₀ c₀ : Kp p) (h : β₀ = π * c₀) : Lmat π hπ β₀ = repInf π hπ * lowU c₀ := by
  refine Units.ext ?_
  show !![(1 : Kp p), 0; -β₀, π] = !![1, 0; 0, π] * !![1, 0; -c₀, 1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

include hπ in

theorem Lmat_eq_repSome (β β' c : Kp p) (hc : π * c = 1 + β * β') :
    Lmat π hπ β = repSome π hπ β' * cof π β β' c hc := by
  refine Units.ext ?_
  show !![(1 : Kp p), 0; -β, π] = !![π, β'; 0, 1] * !![c, -β'; -β, π]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination -hc

end Local

section Residues

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  rcases GroupWithZero.eq_zero_or_unit a with rfl | ⟨u, rfl⟩
  · exact zero_le'
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, (u : WithZero (Multiplicative ℤ)) = WithZero.exp m :=
      ⟨Multiplicative.toAdd (WithZero.unitsWithZeroEquiv u), by
        rw [WithZero.exp]; simp [WithZero.unitsWithZeroEquiv]⟩
    rw [hm] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem exists_eq_mul_of_mem (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ))
    {e : 𝓞 ℚ} (he : e ∈ p.asIdeal) : ∃ c : Op p, algebraMap (𝓞 ℚ) (Op p) e = ϖ * c := by
  have hv : Valued.v ((algebraMap (𝓞 ℚ) (Op p) e : Kp p)) ≤ Valued.v (algebraMap (Op p) (Kp p) ϖ) := by
    rw [hϖ, show ((algebraMap (𝓞 ℚ) (Op p) e : Kp p)) = algebraMap ℚ (Kp p) (algebraMap (𝓞 ℚ) ℚ e) from rfl,
      AdelicBox.valued_algebraMap (𝓞 ℚ) ℚ p e]
    exact le_exp_neg_one_of_lt_one ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 he)
  set c : Kp p := ((algebraMap (𝓞 ℚ) (Op p) e : Kp p)) * (algebraMap (Op p) (Kp p) ϖ)⁻¹ with hc
  have hcint : c ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hc, map_mul, map_inv₀]
    have hne : Valued.v (algebraMap (Op p) (Kp p) ϖ) ≠ 0 := (Valuation.ne_zero_iff _).2 hπ
    calc Valued.v ((algebraMap (𝓞 ℚ) (Op p) e : Kp p)) * (Valued.v (algebraMap (Op p) (Kp p) ϖ))⁻¹
        ≤ Valued.v (algebraMap (Op p) (Kp p) ϖ) * (Valued.v (algebraMap (Op p) (Kp p) ϖ))⁻¹ :=
          mul_le_mul_left hv _
      _ = 1 := mul_inv_cancel₀ hne
  refine ⟨⟨c, hcint⟩, Subtype.ext ?_⟩
  show ((algebraMap (𝓞 ℚ) (Op p) e : Kp p)) = algebraMap (Op p) (Kp p) ϖ * c
  rw [hc, mul_left_comm, mul_inv_cancel₀ hπ, mul_one]

def τ (p : HeightOneSpectrum (𝓞 ℚ)) : Option (𝓞 ℚ ⧸ p.asIdeal) → Option (𝓞 ℚ ⧸ p.asIdeal)
  | none => some 0
  | some r => by
      classical
      haveI := p.isMaximal
      letI := Ideal.Quotient.field p.asIdeal
      exact if r = 0 then none else some (-r⁻¹)

theorem τ_involutive (p : HeightOneSpectrum (𝓞 ℚ)) : Function.Involutive (τ p) := by
  classical
  haveI := p.isMaximal
  letI := Ideal.Quotient.field p.asIdeal
  intro o
  cases o with
  | none => simp [τ]
  | some r =>
    by_cases hr : r = 0
    · simp [τ, hr]
    · have hr' : -r⁻¹ ≠ 0 := by simpa using hr
      simp [τ, hr, hr']

end Residues

section Norms

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem ideleNorm_det_placeEmbed_of_mem_K {κ : GL (Fin 2) (Kp p)} (hκ : κ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p κ)) = 1 := by
  have hX : AdelicLevel.glFin (𝓞 ℚ) ℚ (placeEmbed ℚ p κ) ∈ AdelicLevel.finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [placeEmbed_eq, AdelicDock.glFin_finEmbed]
    exact AdelicLevel.finiteLevelOne_le_finiteLevelZero _ _ _
      ((AdelicDock.localEmbed_mem_finiteLevelOne_iff (𝓞 ℚ) ℚ p κ).2 hκ)
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ _ hX, Fintype.prod_subsingleton _ w0]
  have : archDetNorm (w0) (placeEmbed ℚ p κ) = 1 := by
    unfold archDetNorm
    rw [show AdelicLevel.glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p κ) = 1 from
      (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 (placeEmbed_mem_fin p κ), map_one]
    simp
  rw [this, one_pow]

end Norms

section Main

variable {p : HeightOneSpectrum (𝓞 ℚ)}
variable (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])

theorem ideleNorm_one' : TateGlobal.ideleNorm ℚ 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := ℚ) 1 1
  rw [mul_one] at h
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := ℚ) 1
  have : TateGlobal.ideleNorm ℚ 1 * (TateGlobal.ideleNorm ℚ 1 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h0 | h1
  · exact absurd h0 hpos.ne'
  · linear_combination h1

theorem out_zero_mem : Quotient.out (0 : 𝓞 ℚ ⧸ p.asIdeal) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact Quotient.out_eq' _

theorem star_lemma (Wf Wfd : finiteAdelicGL2Subgroup ℚ → ℂ) (k : finiteAdelicGL2Subgroup ℚ)
    (hk : localAt ℚ p (k : G2) = 1)
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : G2)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (gf : G2) * (k : G2))))
    (g : G2) (m : GL (Fin 2) (Kp p)) :
    Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p m)) =
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : G2)) : ℝ) : ℂ) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p m)) : ℝ) : ℂ) *
          Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (RSCarrier.finFactor g : G2) * (k : G2) *
            placeEmbed ℚ p (T m))) := by
  rw [finFactor_mul_of_mem g (placeEmbed_mem_fin p m), hWfd]
  have e : globalPoints (𝓞 ℚ) ℚ w₀ * (T (RSCarrier.finFactor g : G2) * placeEmbed ℚ p (T m)) * (k : G2) =
      globalPoints (𝓞 ℚ) ℚ w₀ * T (RSCarrier.finFactor g : G2) * (k : G2) * placeEmbed ℚ p (T m) := by
    simp only [mul_assoc, mul_placeEmbed_comm p hk]
  simp only
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, Complex.ofReal_mul, transposeInvN_mul, T_placeEmbed, e, mul_assoc]

theorem key_sum [Fintype (𝓞 ℚ ⧸ p.asIdeal)] (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ))
    (V : G2 → ℂ)
    (h2 : ∀ (x : GL (Fin 2) (Kp p)) (g : G2), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      V (g * placeEmbed ℚ p x) = V g) (Y : G2) :
    (∑ r : 𝓞 ℚ ⧸ p.asIdeal, V (Y * placeEmbed ℚ p (Lmat (algebraMap (Op p) (Kp p) ϖ) hπ
        (algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out r)))))) +
      V (Y * placeEmbed ℚ p (dπ (algebraMap (Op p) (Kp p) ϖ) hπ)) =
    (∑ r : 𝓞 ℚ ⧸ p.asIdeal, V (Y * placeEmbed ℚ p (repSome (algebraMap (Op p) (Kp p) ϖ) hπ
        (algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out r)))))) +
      V (Y * placeEmbed ℚ p (repInf (algebraMap (Op p) (Kp p) ϖ) hπ)) := by
  classical
  haveI := p.isMaximal
  have hπi : (algebraMap (Op p) (Kp p) ϖ) ∈ p.adicCompletionIntegers ℚ := ϖ.2
  set β : 𝓞 ℚ ⧸ p.asIdeal → Kp p :=
    fun r => algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out r)) with hβ
  have hβi : ∀ r, β r ∈ p.adicCompletionIntegers ℚ := fun r => (algebraMap (𝓞 ℚ) (Op p) (Quotient.out r)).2
  set new : Option (𝓞 ℚ ⧸ p.asIdeal) → ℂ := fun o => o.elim (V (Y * placeEmbed ℚ p (dπ (algebraMap (Op p) (Kp p) ϖ) hπ)))
    (fun r => V (Y * placeEmbed ℚ p (Lmat (algebraMap (Op p) (Kp p) ϖ) hπ (β r)))) with hnew
  set old : Option (𝓞 ℚ ⧸ p.asIdeal) → ℂ := fun o => o.elim (V (Y * placeEmbed ℚ p (repInf (algebraMap (Op p) (Kp p) ϖ) hπ)))
    (fun r => V (Y * placeEmbed ℚ p (repSome (algebraMap (Op p) (Kp p) ϖ) hπ (β r)))) with hold
  obtain ⟨c₀, hc₀⟩ := exists_eq_mul_of_mem ϖ hπ hϖ (out_zero_mem (p := p))
  have hβ0 : β 0 = (algebraMap (Op p) (Kp p) ϖ) * (c₀ : Kp p) := by
    show algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out (0 : 𝓞 ℚ ⧸ p.asIdeal))) = _
    rw [hc₀, map_mul]
    rfl
  have hterm : ∀ o, new o = old (τ p o) := by
    intro o
    cases o with
    | none =>
      show V (Y * placeEmbed ℚ p (dπ (algebraMap (Op p) (Kp p) ϖ) hπ)) = V (Y * placeEmbed ℚ p (repSome (algebraMap (Op p) (Kp p) ϖ) hπ (β 0)))
      rw [dπ_eq (algebraMap (Op p) (Kp p) ϖ) hπ (β 0) c₀ hβ0, map_mul, ← mul_assoc, h2 _ _ (unipotent_mem_K (neg_mem c₀.2))]
    | some r =>
      by_cases hr : r = 0
      · subst hr
        have hτ : τ p (some (0 : 𝓞 ℚ ⧸ p.asIdeal)) = none := by simp [τ]
        rw [hτ]
        show V (Y * placeEmbed ℚ p (Lmat (algebraMap (Op p) (Kp p) ϖ) hπ (β 0))) = V (Y * placeEmbed ℚ p (repInf (algebraMap (Op p) (Kp p) ϖ) hπ))
        rw [Lmat_eq_repInf (algebraMap (Op p) (Kp p) ϖ) hπ (β 0) c₀ hβ0, map_mul, ← mul_assoc, h2 _ _ (lowU_mem_K c₀.2)]
      · letI := Ideal.Quotient.field p.asIdeal
        have hτ : τ p (some r) = some (-r⁻¹) := by simp [τ, hr]
        rw [hτ]
        have hmem : 1 + Quotient.out r * Quotient.out (-r⁻¹) ∈ p.asIdeal := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_one, map_mul]
          have e1 : (Ideal.Quotient.mk p.asIdeal (Quotient.out r)) = r := Quotient.out_eq' r
          have e2 : (Ideal.Quotient.mk p.asIdeal (Quotient.out (-r⁻¹))) = -r⁻¹ := Quotient.out_eq' _
          rw [e1, e2, mul_neg, mul_inv_cancel₀ hr, add_neg_cancel]
        obtain ⟨c, hc⟩ := exists_eq_mul_of_mem ϖ hπ hϖ hmem
        have hcπ : (algebraMap (Op p) (Kp p) ϖ) * (c : Kp p) = 1 + β r * β (-r⁻¹) := by
          show _ = 1 + algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out r)) *
            algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out (-r⁻¹)))
          rw [← map_mul, ← map_one (algebraMap (Op p) (Kp p)), ← map_add, ← map_one (algebraMap (𝓞 ℚ) (Op p)),
            ← map_mul, ← map_add, hc, map_mul]
          rfl
        show V (Y * placeEmbed ℚ p (Lmat (algebraMap (Op p) (Kp p) ϖ) hπ (β r))) = V (Y * placeEmbed ℚ p (repSome (algebraMap (Op p) (Kp p) ϖ) hπ (β (-r⁻¹))))
        rw [Lmat_eq_repSome (algebraMap (Op p) (Kp p) ϖ) hπ (β r) (β (-r⁻¹)) c hcπ, map_mul, ← mul_assoc,
          h2 _ _ (cof_mem_K (algebraMap (Op p) (Kp p) ϖ) hcπ hπi (hβi _) (hβi _) c.2)]
  have hsum := Fintype.sum_bijective (τ p) (τ_involutive p).bijective new old hterm
  rw [Fintype.sum_option, Fintype.sum_option] at hsum
  simp only [hnew, hold, Option.elim] at hsum
  linear_combination hsum

theorem psiLoc_eq_of_inv_eq {ψ : AddChar 𝔸 ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ) (x : Kp p) :
    psiLoc ψ p x = psiLoc NumberField.StandardAddChar.psiQ p (-x) := by
  show ψ (NumberField.StandardAddChar.adeleSingleAt ℚ p x) =
    NumberField.StandardAddChar.psiQ (NumberField.StandardAddChar.adeleSingleAt ℚ p (-x))
  rw [← hψQ, AddChar.inv_apply, map_neg (NumberField.StandardAddChar.adeleSingleAt ℚ p), neg_neg]

include hw₀ in

theorem dual_local_relations (Φ : HeckeEigensystem ℚ ℂ) [Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ψ : AddChar 𝔸 ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ))
    (hb0 : Φ.b p ≠ 0)
    (hnorm : TateGlobal.ideleNorm ℚ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (Units.mk0 _ hπ))) = (Ideal.absNorm p.asIdeal : ℝ)⁻¹)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ p (k : G2) = 1)
    (h1 : ∀ (x : Kp p) (g : G2),
      Wf (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) =
        psiLoc NumberField.StandardAddChar.psiQ p x * Wf (RSCarrier.finFactor g))
    (h2 : ∀ (x : GL (Fin 2) (Kp p)) (g : G2), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf (RSCarrier.finFactor g))
    (h3 : ∀ g : G2,
      (∑ r, Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (Op p) (Kp p) ϖ) hπ
          (algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf (algebraMap (Op p) (Kp p) ϖ) hπ))) =
        Φ.a p * Wf (RSCarrier.finFactor g))
    (h4 : ∀ g : G2,
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))) =
        (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf (RSCarrier.finFactor g))
    (Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : G2)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (gf : G2) * (k : G2)))) :
    (∀ (x : Kp p) (g : G2),
      Wfd (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) = psiLoc ψ p x * Wfd (RSCarrier.finFactor g)) ∧
    (∀ (x : GL (Fin 2) (Kp p)) (g : G2), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wfd (RSCarrier.finFactor g)) ∧
    (∀ g : G2,
      (∑ r, Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (Op p) (Kp p) ϖ) hπ
          (algebraMap (Op p) (Kp p) (algebraMap (𝓞 ℚ) (Op p) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
        Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf (algebraMap (Op p) (Kp p) ϖ) hπ))) =
        (Φ.a p / Φ.b p) * Wfd (RSCarrier.finFactor g)) ∧
    (∀ g : G2,
      Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))) =
        ((Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) * Wfd (RSCarrier.finFactor g)) := by
  have hNp : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    have : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    exact_mod_cast this
  have hbN : Φ.b p / (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := div_ne_zero hb0 hNp
  have hfin : ∀ m : GL (Fin 2) (Kp p), placeEmbed ℚ p m ∈ finiteAdelicGL2Subgroup ℚ := placeEmbed_mem_fin p

  have hnS : ∀ β' : Kp p, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p (repSome (algebraMap (Op p) (Kp p) ϖ) hπ β'))) =
      (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := fun β' => by rw [det_placeEmbed, det_repSome]; exact hnorm
  have hnI : TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p (repInf (algebraMap (Op p) (Kp p) ϖ) hπ))) =
      (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := by rw [det_placeEmbed, det_repInf]; exact hnorm
  have hns : TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))) =
      (Ideal.absNorm p.asIdeal : ℝ)⁻¹ * (Ideal.absNorm p.asIdeal : ℝ)⁻¹ := by
    rw [det_placeEmbed, det_scalarPi, map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, hnorm]
  have hnu : ∀ x : Kp p, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p (unipotent x))) = 1 := by
    intro x; rw [det_placeEmbed, det_unipotent, map_one, map_one]; exact ideleNorm_one'

  have hTS : ∀ β' : Kp p, placeEmbed ℚ p (T (repSome (algebraMap (Op p) (Kp p) ϖ) hπ β')) = (placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))⁻¹ * placeEmbed ℚ p (Lmat (algebraMap (Op p) (Kp p) ϖ) hπ β') := by
    intro β'; rw [← map_inv, ← map_mul]; congr 1; exact eq_inv_mul_of_mul_eq (scalarPi_mul_T_repSome (algebraMap (Op p) (Kp p) ϖ) hπ β')
  have hTI : placeEmbed ℚ p (T (repInf (algebraMap (Op p) (Kp p) ϖ) hπ)) = (placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))⁻¹ * placeEmbed ℚ p (dπ (algebraMap (Op p) (Kp p) ϖ) hπ) := by
    rw [← map_inv, ← map_mul]; congr 1; exact eq_inv_mul_of_mul_eq (scalarPi_mul_T_repInf (algebraMap (Op p) (Kp p) ϖ) hπ)
  have star := star_lemma (p := p) w₀ Wf Wfd k hk hWfd

  have h4' : ∀ Y : G2, Wf (RSCarrier.finFactor (Y * (placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))⁻¹)) =
      (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ))⁻¹ * Wf (RSCarrier.finFactor Y) := by
    intro Y
    have := h4 (Y * (placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))⁻¹)
    rw [inv_mul_cancel_right] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hbN, one_mul]
  refine ⟨fun x g => ?_, fun x g hx => ?_, fun g => ?_, fun g => ?_⟩
  ·
    rw [finFactor_mul_of_mem_left g (hfin _), hWfd, hWfd]
    simp only
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, hnu, one_mul, transposeInvN_mul, T_placeEmbed,
      ← mul_assoc (globalPoints (𝓞 ℚ) ℚ w₀), globalPoints_mul_placeEmbed, conj_T_unipotent w₀ hw₀, mul_assoc, mul_assoc,
      h1, psiLoc_eq_of_inv_eq hψQ, ← mul_assoc (globalPoints (𝓞 ℚ) ℚ w₀)]
    ring
  ·
    rw [star, ideleNorm_det_placeEmbed_of_mem_K p hx, h2 _ _ (T_mem_K hx), hWfd]
    push_cast; ring
  ·
    set Xg : G2 := globalPoints (𝓞 ℚ) ℚ w₀ * T (RSCarrier.finFactor g : G2) * (k : G2) with hXg
    have KEY := key_sum ϖ hπ hϖ (fun Z => Wf (RSCarrier.finFactor Z)) h2 (Xg * (placeEmbed ℚ p (scalarPi (algebraMap (Op p) (Kp p) ϖ) hπ))⁻¹)
    simp only [star, hnS, hnI, hTS, hTI]
    rw [← Finset.mul_sum, ← mul_add]
    simp only [← mul_assoc]
    rw [← hXg, KEY, h3, h4' Xg, hWfd]
    push_cast
    field_simp
    try ring
  ·
    rw [star, hns, T_scalarPi, map_inv, h4', hWfd]
    push_cast
    field_simp
    try ring

end Main

end Ws23HeckeLocalDual

end

end Ws23HeckeLocalDualSupply

open UnramifiedWhittaker in

theorem solution
    {p : HeightOneSpectrum (𝓞 ℚ)} (Φ : HeckeEigensystem ℚ ℂ) [Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (ϖ : p.adicCompletionIntegers ℚ) (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hb0 : Φ.b p ≠ 0)
    (hnorm : TateGlobal.ideleNorm ℚ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (Units.mk0 _ hπ))) = (Ideal.absNorm p.asIdeal : ℝ)⁻¹)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ p (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (h1 : ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wf (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) =
        psiLoc NumberField.StandardAddChar.psiQ p x * Wf (RSCarrier.finFactor g))
    (h2 : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf (RSCarrier.finFactor g))
    (h3 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ r, Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        Φ.a p * Wf (RSCarrier.finFactor g))
    (h4 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf (RSCarrier.finFactor g))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ gf : finiteAdelicGL2Subgroup ℚ, Wfd gf =
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ) * (k : AdelicGL2 (𝓞 ℚ) ℚ)))) :
    (∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wfd (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) = psiLoc ψ p x * Wfd (RSCarrier.finFactor g)) ∧
    (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wfd (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ r, Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
        Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        (Φ.a p / Φ.b p) * Wfd (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wfd (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        ((Φ.b p)⁻¹ / (Ideal.absNorm p.asIdeal : ℂ)) * Wfd (RSCarrier.finFactor g)) := by
  exact Ws23HeckeLocalDual.dual_local_relations w₀ hw₀ Φ ψ hψQ ϖ hπ hϖ hb0 hnorm Wf k hk h1 h2 h3 h4 Wfd hWfd

end S_LanglandsTunnell_RankinSelberg_dualTranslate_finWhittaker_local_relations
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_dualTranslate_finWhittaker_local_relations (solution)
