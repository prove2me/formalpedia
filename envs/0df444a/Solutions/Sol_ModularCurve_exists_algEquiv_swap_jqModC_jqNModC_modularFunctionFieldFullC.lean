-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9c437d80-4aab-5435-a379-6ec58af5c94f

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

namespace P2MKcA
namespace WidthB2
namespace SwapFull

p2m_open "ModularCurve~coeffMap_injective ModularCurve.PhiGen Polynomial"

section Transport

variable {R S : Type*} [CommRing R] [CommRing S]

def bev (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries R) : LaurentSeries R :=
  Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y

theorem ringHom_comp_aeval (g : LaurentSeries R →+* LaurentSeries S) (x : LaurentSeries R) :
    g.comp (Polynomial.aeval (R := ℤ) x).toRingHom
      = (Polynomial.aeval (R := ℤ) (g x)).toRingHom := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem map_bev (g : LaurentSeries R →+* LaurentSeries S) (Φ : Polynomial (Polynomial ℤ))
    (x y : LaurentSeries R) :
    g (bev Φ x y) = bev Φ (g x) (g y) := by
  unfold bev
  rw [Polynomial.hom_eval₂, ringHom_comp_aeval]

theorem coeffMap_qExpand (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk,
      map_zero]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_jqNModC (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC]
  rfl

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

end Transport

section Equations

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem bev_rat_eq_zero : bev data.Φ (jqModC ℚ) (jqNModC ℚ N) = 0 :=
  data.eval_eq_zero

theorem bev_rat_swap_eq_zero (hs : EvalSymm data.Φ) :
    bev data.Φ (jqNModC ℚ N) (jqModC ℚ) = 0 := by
  have h := hs (jqNModC ℚ N) (jqModC ℚ)
  unfold bev
  rw [h]
  exact bev_rat_eq_zero data

theorem bev_int_eq_zero : bev data.Φ (jqModC ℤ) (jqNModC ℤ N) = 0 := by
  apply coeffMap_injective (f := Int.castRingHom ℚ) (fun a b h => Int.cast_injective h)
  rw [map_bev, coeffMap_jqModC, coeffMap_jqNModC, map_zero, bev_rat_eq_zero]

theorem bev_int_swap_eq_zero (hs : EvalSymm data.Φ) :
    bev data.Φ (jqNModC ℤ N) (jqModC ℤ) = 0 := by
  apply coeffMap_injective (f := Int.castRingHom ℚ) (fun a b h => Int.cast_injective h)
  rw [map_bev, coeffMap_jqModC, coeffMap_jqNModC, map_zero, bev_rat_swap_eq_zero data hs]

variable (K : Type*) [CommRing K]

theorem bev_eq_zero : bev data.Φ (jqModC K) (jqNModC K N) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom K)) (bev_int_eq_zero data)
  rwa [map_bev, coeffMap_jqModC, coeffMap_jqNModC, map_zero] at h

theorem bev_swap_eq_zero (hs : EvalSymm data.Φ) :
    bev data.Φ (jqNModC K N) (jqModC K) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom K)) (bev_int_swap_eq_zero data hs)
  rwa [map_bev, coeffMap_jqModC, coeffMap_jqNModC, map_zero] at h

end Equations

section Main

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

local notation "Kq" => LaurentSeries K

local notation "EE" => IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

local notation "LL" =>
  IntermediateField.adjoin (↥EE) ({jqNModC K N} : Set (LaurentSeries K))

local notation "FF" => modularFunctionFieldFullC K N

def Hdeg : Prop := Module.finrank (↥EE) (↥LL) = dedekindPsi N

def jE : ↥EE := ⟨jqModC K, IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩

def jF : ↥FF := ⟨jqModC K, jqModC_mem_full K N⟩
def jNF : ↥FF := ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩

def cE : Polynomial ℤ →+* ↥EE := (Polynomial.aeval (R := ℤ) (jE K)).toRingHom

theorem algebraMap_comp_cE :
    (algebraMap (↥EE) Kq).comp (cE K) = (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [cE, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Polynomial.aeval_X]
  rfl

def PE (data : ModularPolynomialData N) : Polynomial ↥EE := data.Φ.map (cE K)

theorem PE_monic (data : ModularPolynomialData N) : (PE K N data).Monic := data.monic.map _

theorem PE_natDegree (data : ModularPolynomialData N) :
    (PE K N data).natDegree = dedekindPsi N := by
  rw [PE, data.monic.natDegree_map]
  exact data.natDegree_eq

theorem aeval_PE (data : ModularPolynomialData N) :
    Polynomial.aeval (jqNModC K N) (PE K N data) = 0 := by
  rw [Polynomial.aeval_def, PE, Polynomial.eval₂_map, algebraMap_comp_cE]
  exact bev_eq_zero data K

theorem isIntegral_jN (data : ModularPolynomialData N) : IsIntegral (↥EE) (jqNModC K N) :=
  ⟨PE K N data, PE_monic K N data, by
    rw [← Polynomial.aeval_def]; exact aeval_PE K N data⟩

theorem minpoly_eq (data : ModularPolynomialData N) (hdeg : Hdeg K N) :
    minpoly (↥EE) (jqNModC K N) = PE K N data := by
  symm
  apply minpoly.unique_of_degree_le_degree_minpoly (↥EE) (jqNModC K N) (PE_monic K N data)
    (aeval_PE K N data)
  rw [Polynomial.degree_eq_natDegree (PE_monic K N data).ne_zero,
    Polynomial.degree_eq_natDegree (minpoly.ne_zero (isIntegral_jN K N data)), PE_natDegree,
    ← IntermediateField.adjoin.finrank (isIntegral_jN K N data)]
  exact_mod_cast hdeg.symm.le

def qEₐ : Kq →ₐ[K] Kq :=
  { qExpand K N with
    commutes' := fun r => by
      show qExpand K N (algebraMap K Kq r) = algebraMap K Kq r
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[scoped simp] theorem qEₐ_apply (x : Kq) : qEₐ K N x = qExpand K N x := rfl

def φ₀ : ↥EE →ₐ[K] Kq := (qEₐ K N).comp (IntermediateField.val EE)

theorem φ₀_apply (x : ↥EE) : φ₀ K N x = qExpand K N (x : Kq) := rfl

theorem φ₀_mem (x : ↥EE) : φ₀ K N x ∈ FF := by
  have hx : φ₀ K N x ∈ (EE).map (qEₐ K N) := ⟨x, x.2, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at hx
  have hle : IntermediateField.adjoin K ({qEₐ K N (jqModC K)} : Set Kq) ≤ FF := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact jqModCd_mem_full K N (dvd_refl N)
  exact hle hx

def iEF : ↥EE →+* ↥FF := (φ₀ K N : ↥EE →+* Kq).codRestrict FF (φ₀_mem K N)

theorem coe_iEF (x : ↥EE) : ((iEF K N x : ↥FF) : Kq) = qExpand K N (x : Kq) := rfl

theorem iEF_jE : iEF K N (jE K) = jNF K N := Subtype.ext rfl

theorem algebraMap_comp_iEF_comp_cE :
    ((algebraMap (↥FF) Kq).comp (iEF K N)).comp (cE K)
      = (Polynomial.aeval (R := ℤ) (jqNModC K N)).toRingHom := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [cE, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Polynomial.aeval_X]
  rfl

theorem hroot (data : ModularPolynomialData N) (hs : EvalSymm data.Φ) (hdeg : Hdeg K N) :
    (minpoly (↥EE) (jqNModC K N)).eval₂ (iEF K N) (jF K N) = 0 := by
  rw [minpoly_eq K N data hdeg]
  apply (algebraMap (↥FF) Kq).injective
  rw [Polynomial.hom_eval₂, PE, Polynomial.eval₂_map, algebraMap_comp_iEF_comp_cE, map_zero]
  exact bev_swap_eq_zero data K hs

omit [NeZero N] in

theorem not_ringChar_dvd (hN : (N : K) ≠ 0) : ¬ ringChar K ∣ N := fun h =>
  hN ((ringChar.spec K N).mpr h)

theorem FF_eq_adjoin_pair (hN : (N : K) ≠ 0) :
    FF = IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set Kq) := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  exact (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) N
    (not_ringChar_dvd K N hN)).symm

theorem restrictScalars_LL (hN : (N : K) ≠ 0) : (LL).restrictScalars K = FF := by
  rw [FF_eq_adjoin_pair K N hN]
  exact IntermediateField.adjoin_simple_adjoin_simple K (jqModC K) (jqNModC K N)

theorem mem_LL_of_mem_FF (hN : (N : K) ≠ 0) {x : Kq} (hx : x ∈ FF) : x ∈ LL := by
  have h : x ∈ (LL).restrictScalars K := by rw [restrictScalars_LL K N hN]; exact hx
  exact h

theorem mem_FF_of_mem_LL (hN : (N : K) ≠ 0) {x : Kq} (hx : x ∈ LL) : x ∈ FF := by
  have h : x ∈ (LL).restrictScalars K := hx
  rwa [restrictScalars_LL K N hN] at h

def toL (hN : (N : K) ≠ 0) : ↥FF →+* ↥LL where
  toFun x := ⟨x, mem_LL_of_mem_FF K N hN x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def toLEquiv (hN : (N : K) ≠ 0) : ↥FF ≃+* ↥LL where
  toFun x := ⟨x, mem_LL_of_mem_FF K N hN x.2⟩
  invFun y := ⟨y, mem_FF_of_mem_LL K N hN y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem toL_jF (hN : (N : K) ≠ 0) : toL K N hN (jF K N) = algebraMap (↥EE) (↥LL) (jE K) := rfl

theorem toL_jNF (hN : (N : K) ≠ 0) :
    toL K N hN (jNF K N) = IntermediateField.AdjoinSimple.gen (↥EE) (jqNModC K N) := rfl

theorem toL_algebraMap (hN : (N : K) ≠ 0) (r : K) :
    toL K N hN (algebraMap K (↥FF) r) = algebraMap (↥EE) (↥LL) (algebraMap K (↥EE) r) := rfl

section Degree

omit [NeZero N] in

theorem EE_le_FF : EE ≤ FF := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact jqModC_mem_full K N

theorem extendScalars_eq_LL (hN : (N : K) ≠ 0) :
    IntermediateField.extendScalars (EE_le_FF K N) = LL := by
  apply IntermediateField.restrictScalars_injective K
  change FF = IntermediateField.restrictScalars K LL
  exact (restrictScalars_LL K N hN).symm

omit [NeZero N] in

theorem adjoin_jF_eq_comap :
    IntermediateField.adjoin K ({(⟨jqModC K, jqModC_mem_full K N⟩ : ↥FF)} : Set ↥FF) =
      (EE).comap (IntermediateField.val FF) := by
  apply IntermediateField.lift_injective
  erw [IntermediateField.lift_adjoin_simple]
  change EE = ((EE).comap (IntermediateField.val FF)).map (IntermediateField.val FF)
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val,
    inf_eq_left.mpr (EE_le_FF K N)]

theorem hdeg_of (hN : (N : K) ≠ 0) : Hdeg K N := by
  unfold Hdeg
  calc Module.finrank (↥EE) (↥LL)
      = Module.finrank (↥EE) (↥(IntermediateField.extendScalars (EE_le_FF K N))) := by
          rw [extendScalars_eq_LL K N hN]
    _ = IntermediateField.relfinrank EE FF :=
          (IntermediateField.relfinrank_eq_finrank_of_le (EE_le_FF K N)).symm
    _ = IntermediateField.relfinrank EE (IntermediateField.val FF).fieldRange := by
          rw [IntermediateField.fieldRange_val]
    _ = Module.finrank (↥((EE).comap (IntermediateField.val FF))) (↥FF) :=
          (IntermediateField.finrank_comap EE (IntermediateField.val FF)).symm
    _ = dedekindPsi N := by
          have h8 :=
            ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN
          rw [adjoin_jF_eq_comap K N] at h8
          exact h8

end Degree

def σL (data : ModularPolynomialData N) (hs : EvalSymm data.Φ) (hdeg : Hdeg K N) :
    ↥LL →+* ↥FF :=
  (AdjoinRoot.lift (iEF K N) (jF K N) (hroot K N data hs hdeg)).comp
    (IntermediateField.adjoinRootEquivAdjoin (↥EE)
      (isIntegral_jN K N data)).symm.toRingEquiv.toRingHom

theorem σL_gen (data : ModularPolynomialData N) (hs : EvalSymm data.Φ) (hdeg : Hdeg K N) :
    σL K N data hs hdeg (IntermediateField.AdjoinSimple.gen (↥EE) (jqNModC K N)) = jF K N := by
  have h : (IntermediateField.adjoinRootEquivAdjoin (↥EE) (isIntegral_jN K N data)).symm
      (IntermediateField.AdjoinSimple.gen (↥EE) (jqNModC K N))
        = AdjoinRoot.root (minpoly (↥EE) (jqNModC K N)) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (IntermediateField.adjoinRootEquivAdjoin_apply_root (↥EE) (isIntegral_jN K N data)).symm
  simp only [σL, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, h, AdjoinRoot.lift_root]

theorem σL_algebraMap (data : ModularPolynomialData N) (hs : EvalSymm data.Φ) (hdeg : Hdeg K N)
    (e : ↥EE) :
    σL K N data hs hdeg (algebraMap (↥EE) (↥LL) e) = iEF K N e := by
  simp only [σL, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.lift_of]

def σ₁ (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) : ↥FF →ₐ[K] ↥FF :=
  { (σL K N data hs hdeg).comp (toL K N hN) with
    commutes' := fun r => by
      show σL K N data hs hdeg (toL K N hN (algebraMap K (↥FF) r)) = algebraMap K (↥FF) r
      rw [toL_algebraMap, σL_algebraMap]
      apply Subtype.ext
      show qExpand K N (algebraMap K Kq r) = algebraMap K Kq r
      exact (qEₐ K N).commutes r }

theorem σ₁_apply (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) (x : ↥FF) :
    σ₁ K N hN data hs hdeg x = σL K N data hs hdeg (toL K N hN x) := rfl

theorem σ₁_jF (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) : σ₁ K N hN data hs hdeg (jF K N) = jNF K N := by
  rw [σ₁_apply, toL_jF, σL_algebraMap, iEF_jE]

theorem σ₁_jNF (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) : σ₁ K N hN data hs hdeg (jNF K N) = jF K N := by
  rw [σ₁_apply, toL_jNF, σL_gen]

theorem σ₁_comp_σ₁ (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) :
    (σ₁ K N hN data hs hdeg).comp (σ₁ K N hN data hs hdeg) = AlgHom.id K (↥FF) := by
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := K) (S := FF)
    (s := ({jqModC K, jqNModC K N} : Set (LaurentSeries K))) (FF_eq_adjoin_pair K N hN) ?_
  intro x hx
  rcases hx with rfl | hx
  · show σ₁ K N hN data hs hdeg (σ₁ K N hN data hs hdeg (jF K N)) = jF K N
    rw [σ₁_jF, σ₁_jNF]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    show σ₁ K N hN data hs hdeg (σ₁ K N hN data hs hdeg (jNF K N)) = jNF K N
    rw [σ₁_jNF, σ₁_jF]

def σ (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) : ↥FF ≃ₐ[K] ↥FF :=
  AlgEquiv.ofAlgHom (σ₁ K N hN data hs hdeg) (σ₁ K N hN data hs hdeg)
    (σ₁_comp_σ₁ K N hN data hs hdeg) (σ₁_comp_σ₁ K N hN data hs hdeg)

theorem σ_apply (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) (hs : EvalSymm data.Φ)
    (hdeg : Hdeg K N) (x : ↥FF) : σ K N hN data hs hdeg x = σ₁ K N hN data hs hdeg x := rfl

theorem main_of_one_lt (hN : (N : K) ≠ 0) (h1 : 1 < N) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      σ ⟨jqModC K, jqModC_mem_full K N⟩ = ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ ∧
      σ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ = ⟨jqModC K, jqModC_mem_full K N⟩ ∧
      ∀ x, σ (σ x) = x := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hs : EvalSymm data.Φ := ModularCurve.ModularPolynomialData.evalSymm_of_one_lt N h1 data
  have hdeg : Hdeg K N := hdeg_of K N hN
  refine ⟨σ K N hN data hs hdeg, ?_, ?_, ?_⟩
  · rw [σ_apply]; exact σ₁_jF K N hN data hs hdeg
  · rw [σ_apply]; exact σ₁_jNF K N hN data hs hdeg
  · intro x
    rw [σ_apply, σ_apply]
    exact congrArg (fun f : ↥FF →ₐ[K] ↥FF => f x) (σ₁_comp_σ₁ K N hN data hs hdeg)

end Main

theorem main (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      σ ⟨jqModC K, jqModC_mem_full K N⟩ = ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ ∧
      σ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ = ⟨jqModC K, jqModC_mem_full K N⟩ ∧
      ∀ x, σ (σ x) = x := by
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · exact main_of_one_lt K N hN h1
  · have hN1 : N = 1 := le_antisymm h1 (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    subst hN1
    refine ⟨AlgEquiv.refl, ?_, ?_, fun _ => rfl⟩
    · exact Subtype.ext (jqNModC_one K).symm
    · exact Subtype.ext (jqNModC_one K)

end P2MKcA.WidthB2.SwapFull
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA.WidthB2 P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA.WidthB2.SwapFull"
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA.WidthB2"
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA.WidthB2 P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.P2MKcA.WidthB2.SwapFull"

p2m_open "ModularCurve~coeffMap_injective"

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      σ ⟨jqModC K, jqModC_mem_full K N⟩ = ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ ∧
      σ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ = ⟨jqModC K, jqModC_mem_full K N⟩ ∧
      ∀ x, σ (σ x) = x :=
  P2MKcA.WidthB2.SwapFull.main K N hN

end S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC (solution)
