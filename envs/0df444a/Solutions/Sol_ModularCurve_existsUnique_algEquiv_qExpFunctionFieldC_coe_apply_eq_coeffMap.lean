-- Prove2me | solution 1 for ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9d959f64-b9af-5340-82e7-af7884464116

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve IntermediateField HahnSeries Module
open scoped MatrixGroups

namespace QExpAutBaseChange

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem coeff_smul' {L : Type*} [Field L] (r : L) (x : LaurentSeries L) (n : ℤ) :
    (r • x).coeff n = r * x.coeff n := by
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) : coeffMap φ (intSeriesC K₀ p) = intSeriesC K p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map φ),
    ← PowerSeries.map_comp, RingHom.ext_int (φ.comp (Int.castRingHom K₀)) (Int.castRingHom K)]

theorem coeffMap_injective : Function.Injective (coeffMap φ) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries K => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact φ.injective this

include φ in
theorem intSeriesC_ne_zero_iff (p : PowerSeries ℤ) : intSeriesC K p ≠ 0 ↔ intSeriesC K₀ p ≠ 0 := by
  rw [← coeffMap_intSeriesC φ]
  refine ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h ?_⟩
  exact coeffMap_injective φ (h0.trans (map_zero _).symm)

theorem coeffMap_algebraMap' (c : K₀) :
    coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) = algebraMap K (LaurentSeries K) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]

theorem intFormRatiosC_eq_image :
    intFormRatiosC K Γ = coeffMap φ '' intFormRatiosC K₀ Γ := by
  ext y
  constructor
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC K₀ pf / intSeriesC K₀ pg,
      ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff φ pg).mp hg0, rfl⟩, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  · rintro ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff φ pg).mpr hg0, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coeffMap_mem {x : LaurentSeries K₀} (hx : x ∈ qExpFunctionFieldC K₀ Γ) :
    coeffMap φ x ∈ qExpFunctionFieldC K Γ := by
  let T : Subfield (LaurentSeries K₀) := (qExpFunctionFieldC K Γ).toSubfield.comap (coeffMap φ)
  have hgen : intFormRatiosC K₀ Γ ⊆ (T : Set (LaurentSeries K₀)) := by
    intro y hy
    change coeffMap φ y ∈ qExpFunctionFieldC K Γ
    apply intFormRatiosC_subset K Γ
    rw [intFormRatiosC_eq_image φ Γ]
    exact ⟨y, hy, rfl⟩
  have hconst : Set.range (algebraMap K₀ (LaurentSeries K₀)) ⊆ (T : Set (LaurentSeries K₀)) := by
    rintro y ⟨c, rfl⟩
    change coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) ∈ qExpFunctionFieldC K Γ
    rw [coeffMap_algebraMap']
    exact (qExpFunctionFieldC K Γ).algebraMap_mem _
  have hle : (qExpFunctionFieldC K₀ Γ).toSubfield ≤ T := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hconst hgen)
  exact hle hx

abbrev E₀ : Type _ := ↥(qExpFunctionFieldC K₀ Γ)
abbrev E : Type _ := ↥(qExpFunctionFieldC K Γ)

def iota : E₀ (K₀ := K₀) Γ →+* E (K := K) Γ where
  toFun y := ⟨coeffMap φ y, coeffMap_mem φ Γ y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_iota (y : E₀ (K₀ := K₀) Γ) :
    ((iota φ Γ y : E (K := K) Γ) : LaurentSeries K) = coeffMap φ y := rfl

theorem iota_injective : Function.Injective (iota φ Γ) := fun a b h =>
  Subtype.ext (coeffMap_injective φ (congrArg Subtype.val h))

theorem iota_smul (c : K₀) (y : E₀ (K₀ := K₀) Γ) : iota φ Γ (c • y) = φ c • iota φ Γ y := by
  apply Subtype.ext
  rw [coe_iota, IntermediateField.coe_smul, IntermediateField.coe_smul, Algebra.smul_def, Algebra.smul_def,
    map_mul, coeffMap_algebraMap', coe_iota]

theorem linearIndependent_coeffMap {ι : Type*} {v : ι → LaurentSeries K₀} (hv : LinearIndependent K₀ v) :
    LinearIndependent K (fun i => coeffMap φ (v i)) := by
  classical
  letI : Algebra K₀ K := φ.toAlgebra
  have hφ : ∀ c : K₀, algebraMap K₀ K c = φ c := fun _ => rfl
  rw [linearIndependent_iff']
  intro s c hsum i hi
  let W : Submodule K₀ K := Submodule.span K₀ (Set.range fun j : s => c j)
  haveI : Module.Finite K₀ W := Module.Finite.span_of_finite K₀ (Set.finite_range _)
  let b := Module.finBasis K₀ W
  have hcW : ∀ j : s, c j ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  let a : s → Fin (Module.finrank K₀ W) → K₀ := fun j l => b.repr ⟨c j, hcW j⟩ l
  have hca : ∀ j : s, c j = ∑ l, a j l • (b l : K) := by
    intro j
    have h1 := b.sum_repr ⟨c j, hcW j⟩
    have h2 := congrArg (Submodule.subtype W) h1
    rw [map_sum] at h2
    simp only [Submodule.subtype_apply, Submodule.coe_smul] at h2
    exact h2.symm
  have hcoeff : ∀ n : ℤ, ∑ j ∈ s, c j * φ ((v j).coeff n) = 0 := by
    intro n
    have := congrArg (fun x : LaurentSeries K => x.coeff n) hsum
    simpa [HahnSeries.coeff_sum, coeff_smul', coeffMap_coeff] using this
  have hbi : LinearIndependent K₀ (fun l' => (b l' : K)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hv' : LinearIndependent K₀ (fun j : s => v j) := hv.comp _ Subtype.val_injective
  have hrel : ∀ l, ∑ j : s, a j l • v j = 0 := by
    intro l
    ext n
    have h1 : ∑ l', (∑ j : s, a j l' * (v j).coeff n) • (b l' : K) = 0 := by
      have h0 := hcoeff n
      rw [← Finset.sum_coe_sort] at h0
      simp_rw [hca, Finset.sum_mul] at h0
      rw [Finset.sum_comm] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, hφ]; ring
    have := Fintype.linearIndependent_iff.mp hbi (fun l' => ∑ j : s, a j l' * (v j).coeff n) h1 l
    rw [HahnSeries.coeff_sum]
    simpa [coeff_smul'] using this
  have ha : ∀ (j : s) l, a j l = 0 := fun j l =>
    Fintype.linearIndependent_iff.mp hv' (fun j => a j l) (hrel l) j
  rw [show c i = c (⟨i, hi⟩ : s) from rfl, hca]
  simp [ha]

def Rsub : Subalgebra K (E (K := K) Γ) where
  carrier := Submodule.span K (Set.range (iota φ Γ))
  mul_mem' {a b} ha hb := by
    change a * b ∈ Submodule.span K (Set.range (iota φ Γ))
    refine Submodule.span_induction (p := fun a _ => a * b ∈ Submodule.span K (Set.range (iota φ Γ)))
      ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨y, rfl⟩
      refine Submodule.span_induction (p := fun b _ => iota φ Γ y * b ∈ Submodule.span K (Set.range (iota φ Γ)))
        ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨z, rfl⟩
        rw [← map_mul]
        exact Submodule.subset_span ⟨y * z, rfl⟩
      · show iota φ Γ y * 0 ∈ _
        rw [mul_zero]; exact zero_mem _
      · intro u v _ _ hu hv
        show iota φ Γ y * (u + v) ∈ _
        rw [mul_add]; exact add_mem hu hv
      · intro c u _ hu
        show iota φ Γ y * (c • u) ∈ _
        rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
    · show (0 : E (K := K) Γ) * b ∈ _
      rw [zero_mul]; exact zero_mem _
    · intro u v _ _ hu hv
      show (u + v) * b ∈ _
      rw [add_mul]; exact add_mem hu hv
    · intro c u _ hu
      show (c • u) * b ∈ _
      rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  add_mem' {a b} ha hb := add_mem ha hb
  algebraMap_mem' c := by
    change algebraMap K (E Γ) c ∈ Submodule.span K (Set.range (iota φ Γ))
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨1, ?_⟩)
    rw [map_one]

theorem mem_Rsub_iff (a : E (K := K) Γ) : a ∈ Rsub φ Γ ↔ a ∈ Submodule.span K (Set.range (iota φ Γ)) := Iff.rfl

theorem iota_mem_Rsub (y : E₀ (K₀ := K₀) Γ) : iota φ Γ y ∈ Rsub φ Γ :=
  Submodule.subset_span ⟨y, rfl⟩

def iotaR (y : E₀ (K₀ := K₀) Γ) : Rsub φ Γ := ⟨iota φ Γ y, iota_mem_Rsub φ Γ y⟩

@[scoped simp] theorem coe_iotaR (y : E₀ (K₀ := K₀) Γ) : ((iotaR φ Γ y : Rsub φ Γ) : E (K := K) Γ) = iota φ Γ y := rfl

theorem iotaR_mul (y z : E₀ (K₀ := K₀) Γ) : iotaR φ Γ (y * z) = iotaR φ Γ y * iotaR φ Γ z :=
  Subtype.ext (map_mul _ _ _)

theorem iotaR_one : iotaR φ Γ (1 : E₀ (K₀ := K₀) Γ) = 1 := Subtype.ext (map_one _)

def iotaRsl : E₀ (K₀ := K₀) Γ →ₛₗ[φ] Rsub φ Γ where
  toFun := iotaR φ Γ
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := by
    apply Subtype.ext
    rw [Subalgebra.coe_smul, coe_iotaR, coe_iotaR, iota_smul]

@[scoped simp] theorem iotaRsl_apply (y : E₀ (K₀ := K₀) Γ) : iotaRsl φ Γ y = iotaR φ Γ y := rfl

section WithBasis

variable {ιb : Type*} (b : Basis ιb K₀ (E₀ (K₀ := K₀) Γ))

theorem linearIndependent_val_comp {ι : Type*} {v : ι → E₀ (K₀ := K₀) Γ} (hv : LinearIndependent K₀ v) :
    LinearIndependent K₀ (fun j => ((v j : E₀ Γ) : LaurentSeries K₀)) :=
  hv.map' (IntermediateField.val _).toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

def w (j : ιb) : Rsub φ Γ := iotaR φ Γ (b j)

def toLaurent : Rsub φ Γ →ₗ[K] LaurentSeries K where
  toFun r := ((r : E (K := K) Γ) : LaurentSeries K)
  map_add' a b := by
    rw [Subalgebra.coe_add, IntermediateField.coe_add]
  map_smul' c a := by
    rw [RingHom.id_apply, Subalgebra.coe_smul, IntermediateField.coe_smul]

theorem toLaurent_apply (r : Rsub φ Γ) : toLaurent φ Γ r = ((r : E (K := K) Γ) : LaurentSeries K) := rfl

theorem toLaurent_w (j : ιb) :
    toLaurent φ Γ (w φ Γ b j) = coeffMap φ ((b j : E₀ Γ) : LaurentSeries K₀) := rfl

theorem linearIndependent_w : LinearIndependent K (w φ Γ b) := by

  have h0 : LinearIndependent K₀ (fun j => ((b j : E₀ Γ) : LaurentSeries K₀)) :=
    linearIndependent_val_comp Γ b.linearIndependent
  have h1 := linearIndependent_coeffMap φ h0
  refine LinearIndependent.of_comp (toLaurent φ Γ) ?_
  have hfun : (⇑(toLaurent φ Γ) ∘ w φ Γ b) =
      fun j => coeffMap φ ((b j : E₀ Γ) : LaurentSeries K₀) :=
    funext fun j => toLaurent_w φ Γ b j
  rw [hfun]
  exact h1

def iotaSL : E₀ (K₀ := K₀) Γ →ₛₗ[φ] E (K := K) Γ where
  toFun := iota φ Γ
  map_add' a b := map_add _ _ _
  map_smul' c a := iota_smul φ Γ c a

@[scoped simp] theorem iotaSL_apply (y : E₀ (K₀ := K₀) Γ) : iotaSL φ Γ y = iota φ Γ y := rfl

theorem iota_mem_span (y : E₀ (K₀ := K₀) Γ) :
    iota φ Γ y ∈ Submodule.span K (Set.range fun j => iota φ Γ (b j)) := by
  have key : ∀ l : ιb →₀ K₀,
      iotaSL φ Γ (Finsupp.linearCombination K₀ b l) ∈ Submodule.span K (Set.range fun j => iota φ Γ (b j)) := by
    intro l
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun j _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := key (b.repr y)
  rwa [b.linearCombination_repr y] at this

theorem range_val_w : Set.range (fun j => ((w φ Γ b j : Rsub φ Γ) : E (K := K) Γ)) =
    Set.range fun j => iota φ Γ (b j) := rfl

theorem span_w : ⊤ ≤ Submodule.span K (Set.range (w φ Γ b)) := by
  intro r _
  have h1 : (r : E (K := K) Γ) ∈ Submodule.span K (Set.range (iota φ Γ)) := r.2
  have h2 : Submodule.span K (Set.range (iota φ Γ)) ≤ Submodule.span K (Set.range fun j => iota φ Γ (b j)) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨y, rfl⟩
      exact iota_mem_span φ Γ b y)
  have h3 : Submodule.span K (Set.range fun j => iota φ Γ (b j)) =
      (Submodule.span K (Set.range (w φ Γ b))).map (Rsub φ Γ).val.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h4 := h2 h1
  rw [h3, Submodule.mem_map] at h4
  obtain ⟨r', hr', hval⟩ := h4
  have : r' = r := Subtype.ext hval
  rw [← this]
  exact hr'

def bR : Basis ιb K (Rsub φ Γ) :=
  Basis.mk (linearIndependent_w φ Γ b) (span_w φ Γ b)

theorem bR_apply (j : ιb) : bR φ Γ b j = iotaR φ Γ (b j) :=
  Basis.mk_apply _ _ j

section Sigma

variable (σ₀ : E₀ (K₀ := K₀) Γ ≃ₐ[K₀] E₀ (K₀ := K₀) Γ)

def sigmaR : Rsub φ Γ →ₗ[K] Rsub φ Γ :=
  (bR φ Γ b).constr K fun j => iotaR φ Γ (σ₀ (b j))

theorem sigmaR_bR (j : ιb) :
    sigmaR φ Γ b σ₀ (bR φ Γ b j) = iotaR φ Γ (σ₀ (b j)) :=
  Basis.constr_basis _ _ _ j

theorem sigmaR_iotaR (y : E₀ (K₀ := K₀) Γ) : sigmaR φ Γ b σ₀ (iotaR φ Γ y) = iotaR φ Γ (σ₀ y) := by
  have key : (sigmaR φ Γ b σ₀).comp (iotaRsl φ Γ) = (iotaRsl φ Γ).comp σ₀.toLinearMap := by
    refine b.ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, iotaRsl_apply, ← bR_apply, sigmaR_bR]
    rfl
  have := congrArg (fun f => f y) key
  simpa using this

theorem sigmaR_one : sigmaR φ Γ b σ₀ 1 = 1 := by
  rw [← iotaR_one, sigmaR_iotaR, map_one, iotaR_one]

theorem sigmaR_mul (r s : Rsub φ Γ) : sigmaR φ Γ b σ₀ (r * s) = sigmaR φ Γ b σ₀ r * sigmaR φ Γ b σ₀ s := by
  have key : (LinearMap.mul K (Rsub φ Γ)).compr₂ (sigmaR φ Γ b σ₀) =
      (LinearMap.mul K (Rsub φ Γ)).compl₁₂ (sigmaR φ Γ b σ₀) (sigmaR φ Γ b σ₀) := by
    refine (bR φ Γ b).ext fun i => (bR φ Γ b).ext fun j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    rw [bR_apply, bR_apply, ← iotaR_mul, sigmaR_iotaR, sigmaR_iotaR, sigmaR_iotaR, map_mul, iotaR_mul]
  have := congrArg (fun f => f r s) key
  simpa using this

theorem sigmaR_symm_sigmaR (r : Rsub φ Γ) : sigmaR φ Γ b σ₀.symm (sigmaR φ Γ b σ₀ r) = r := by
  have key : (sigmaR φ Γ b σ₀.symm).comp (sigmaR φ Γ b σ₀) = LinearMap.id := by
    refine (bR φ Γ b).ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, bR_apply, sigmaR_iotaR, sigmaR_iotaR,
      AlgEquiv.symm_apply_apply]
  exact congrArg (fun f => f r) key

def sigmaRequiv : Rsub φ Γ ≃ₗ[K] Rsub φ Γ :=
  LinearEquiv.ofLinear (sigmaR φ Γ b σ₀) (sigmaR φ Γ b σ₀.symm)
    (LinearMap.ext fun r => by simpa using sigmaR_symm_sigmaR φ Γ b σ₀.symm r)
    (LinearMap.ext fun r => sigmaR_symm_sigmaR φ Γ b σ₀ r)

def eR : Rsub φ Γ ≃ₐ[K] Rsub φ Γ :=
  AlgEquiv.ofLinearEquiv (sigmaRequiv φ Γ b σ₀) (sigmaR_one φ Γ b σ₀) (sigmaR_mul φ Γ b σ₀)

theorem eR_apply (r : Rsub φ Γ) : eR φ Γ b σ₀ r = sigmaR φ Γ b σ₀ r := rfl

theorem eR_iotaR (y : E₀ (K₀ := K₀) Γ) : eR φ Γ b σ₀ (iotaR φ Γ y) = iotaR φ Γ (σ₀ y) :=
  sigmaR_iotaR φ Γ b σ₀ y

end Sigma

theorem exists_Rsub_of_mem_closure {t : LaurentSeries K}
    (ht : t ∈ Subring.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ)) :
    ∃ r : Rsub φ Γ, ((r : E (K := K) Γ) : LaurentSeries K) = t := by
  let Rimg : Subring (LaurentSeries K) :=
    (Rsub φ Γ).toSubring.map ((IntermediateField.val (qExpFunctionFieldC K Γ)) : E Γ →+* LaurentSeries K)
  have hle : Subring.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ) ≤ Rimg := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨c, rfl⟩ | hy)
    · exact ⟨algebraMap K (E Γ) c, (Rsub φ Γ).algebraMap_mem c, rfl⟩
    · rw [intFormRatiosC_eq_image φ Γ] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ⟨iota φ Γ ⟨y₀, intFormRatiosC_subset K₀ Γ hy₀⟩, iota_mem_Rsub φ Γ _, rfl⟩
  obtain ⟨r, hr, hrt⟩ := hle ht
  exact ⟨⟨r, hr⟩, hrt⟩

scoped instance isFractionRing_Rsub : IsFractionRing (Rsub φ Γ) (E (K := K) Γ) where
  map_units := by
    rintro ⟨s, hs⟩
    have hs0 : (s : E (K := K) Γ) ≠ 0 := fun h => nonZeroDivisors.ne_zero hs (Subtype.ext (by rw [h]; rfl))
    exact isUnit_iff_ne_zero.mpr hs0
  surj := by
    intro z
    have hz : (z : LaurentSeries K) ∈ (IntermediateField.adjoin K (intFormRatiosC K Γ)).toSubfield := z.2
    rw [IntermediateField.adjoin_toSubfield, Subfield.mem_closure_iff] at hz
    obtain ⟨y, hy, y', hy', hyz⟩ := hz
    obtain ⟨a, ha⟩ := exists_Rsub_of_mem_closure φ Γ hy
    obtain ⟨s, hs⟩ := exists_Rsub_of_mem_closure φ Γ hy'
    rw [← ha, ← hs] at hyz
    by_cases hs0 : ((s : E (K := K) Γ) : LaurentSeries K) = 0
    · refine ⟨(0, 1), ?_⟩
      have hz0 : z = 0 := by
        apply Subtype.ext
        rw [← hyz, hs0, div_zero]
        rfl
      rw [hz0]
      simp
    · have hsE : (s : E (K := K) Γ) ≠ 0 := fun h => hs0 (by rw [h]; rfl)
      have hsR : s ≠ 0 := fun h => hsE (by rw [h]; rfl)
      refine ⟨(a, ⟨s, mem_nonZeroDivisors_of_ne_zero hsR⟩), ?_⟩
      show z * (s : E (K := K) Γ) = (a : E (K := K) Γ)
      apply Subtype.ext
      rw [MulMemClass.coe_mul, ← hyz, div_mul_cancel₀ _ hs0]
  exists_of_eq := by
    intro x y h
    have hxy : x = y := Subtype.ext h
    exact ⟨1, by rw [hxy]⟩

section Sigma

variable (σ₀ : E₀ (K₀ := K₀) Γ ≃ₐ[K₀] E₀ (K₀ := K₀) Γ)

def sigmaE : E (K := K) Γ ≃+* E (K := K) Γ :=
  IsFractionRing.ringEquivOfRingEquiv (eR φ Γ b σ₀ : Rsub φ Γ ≃+* Rsub φ Γ)

theorem sigmaE_coe (r : Rsub φ Γ) : sigmaE φ Γ b σ₀ (r : E (K := K) Γ) = (eR φ Γ b σ₀ r : Rsub φ Γ) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (eR φ Γ b σ₀ : Rsub φ Γ ≃+* Rsub φ Γ) r

theorem eR_ringEquiv_apply (r : Rsub φ Γ) : (eR φ Γ b σ₀ : Rsub φ Γ ≃+* Rsub φ Γ) r = eR φ Γ b σ₀ r := rfl

theorem sigmaE_algebraMap (c : K) : sigmaE φ Γ b σ₀ (algebraMap K (E Γ) c) = algebraMap K (E Γ) c := by
  rw [IsScalarTower.algebraMap_apply K (Rsub φ Γ) (E Γ) c, sigmaE,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, eR_ringEquiv_apply, AlgEquiv.commutes]

def sigma : E (K := K) Γ ≃ₐ[K] E (K := K) Γ :=
  AlgEquiv.ofRingEquiv (f := sigmaE φ Γ b σ₀) (sigmaE_algebraMap φ Γ b σ₀)

theorem sigma_iota (y : E₀ (K₀ := K₀) Γ) : sigma φ Γ b σ₀ (iota φ Γ y) = iota φ Γ (σ₀ y) := by
  change sigmaE φ Γ b σ₀ ((iotaR φ Γ y : Rsub φ Γ) : E (K := K) Γ) = _
  rw [sigmaE_coe, eR_iotaR]
  rfl

end Sigma

theorem algEquiv_eq_of_iota (τ τ' : E (K := K) Γ ≃ₐ[K] E (K := K) Γ)
    (h : ∀ y : E₀ (K₀ := K₀) Γ, τ (iota φ Γ y) = τ' (iota φ Γ y)) : τ = τ' := by

  let Q : IntermediateField K (E (K := K) Γ) :=
    { carrier := {z | τ z = τ' z}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      zero_mem' := by simp
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, AlgEquiv.commutes]
      inv_mem' := fun x hx => by
        simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx] }
  have hgen : qExpFunctionFieldC K Γ ≤ IntermediateField.lift Q := by
    conv_lhs => rw [qExpFunctionFieldC]
    rw [adjoin_le_iff]
    intro s hs
    have hs' := hs
    rw [intFormRatiosC_eq_image φ Γ] at hs'
    obtain ⟨s₀, hs₀, rfl⟩ := hs'
    have hmem : (⟨_, intFormRatiosC_subset K Γ hs⟩ : E (K := K) Γ) ∈ Q := by
      change τ _ = τ' _
      have : (⟨_, intFormRatiosC_subset K Γ hs⟩ : E (K := K) Γ) = iota φ Γ ⟨s₀, intFormRatiosC_subset K₀ Γ hs₀⟩ :=
        Subtype.ext rfl
      rw [this]
      exact h _
    exact (mem_lift (⟨_, intFormRatiosC_subset K Γ hs⟩ : E (K := K) Γ)).mpr hmem
  refine AlgEquiv.ext fun z => ?_
  have hz : (z : LaurentSeries K) ∈ IntermediateField.lift Q := hgen z.2
  exact (mem_lift z).mp hz

end WithBasis

end QExpAutBaseChange
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap.QExpAutBaseChange"

theorem solution
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ₀ : ModularCurve.qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] ModularCurve.qExpFunctionFieldC K₀ Γ) :
    ∃! σ : ModularCurve.qExpFunctionFieldC K Γ ≃ₐ[K] ModularCurve.qExpFunctionFieldC K Γ,
      ∀ (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ),
        (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀) →
        ((σ x : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) =
          ModularCurve.coeffMap φ ((σ₀ x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) : LaurentSeries K₀) := by
  refine ⟨QExpAutBaseChange.sigma φ Γ (Module.Basis.ofVectorSpace K₀ _) σ₀, ?_, ?_⟩
  · intro x₀ x hx
    have : x = QExpAutBaseChange.iota φ Γ x₀ := Subtype.ext hx
    rw [this, QExpAutBaseChange.sigma_iota]
    rfl
  · intro τ hτ
    refine QExpAutBaseChange.algEquiv_eq_of_iota φ Γ τ _ fun y => ?_
    apply Subtype.ext
    rw [hτ y _ rfl, QExpAutBaseChange.sigma_iota]
    rfl

end
end S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap (solution)
