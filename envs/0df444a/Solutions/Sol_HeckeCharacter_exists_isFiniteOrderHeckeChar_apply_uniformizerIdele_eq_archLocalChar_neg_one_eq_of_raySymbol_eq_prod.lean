-- Prove2me | solution 1 for HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/576b9e08-959d-5eea-9d4f-bc1ad91bb95a

import Mathlib
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_LT_HeckeChar_exists_heckeCharOfRayClassChar
import Theorems.Thm_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign
import Theorems.Thm_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff
import Theorems.Thm_HeckeCharacter_archRealProjTau_unitsMap_algebraMap
import Theorems.Thm_HeckeCharacter_coe_fadContentHom_projFin_unitsMap_algebraMap
import Theorems.Thm_HeckeCharacter_raySymbolUnitsHom_fadContentHom
import Theorems.Thm_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Deep.NTSupply NumberField.AdelicLevel LanglandsTunnell.P2.Artin

open scoped nonZeroDivisors

noncomputable section

namespace RayClassSignHeckeCharSol

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝔸Kf" => FiniteAdeleRing (𝓞 K) K

def finUnit : (𝔸Kf)ˣ →* (𝔸K)ˣ := Units.map (finIncl (𝓞 K) K)

theorem finUnit_val_fst (y : (𝔸Kf)ˣ) : ((finUnit K y : (𝔸K)ˣ) : 𝔸K).1 = 1 := rfl

theorem finUnit_val_snd (y : (𝔸Kf)ˣ) : ((finUnit K y : (𝔸K)ˣ) : 𝔸K).2 = (y : 𝔸Kf) := rfl

theorem projFin_finUnit (y : (𝔸Kf)ˣ) : projFin K (finUnit K y) = y := by
  refine Units.ext ?_
  rfl

theorem projFin_val (u : (𝔸K)ˣ) : ((projFin K u : (𝔸Kf)ˣ) : 𝔸Kf) = (u : 𝔸K).2 := rfl

def compUnit (y : (𝔸Kf)ˣ) (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 ((y : 𝔸Kf) v) (by
    intro h
    exact valued_ne_zero_of_unit K y v (by rw [h, map_zero]))

@[scoped simp] theorem compUnit_val (y : (𝔸Kf)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (compUnit K y v : v.adicCompletion K) = (y : 𝔸Kf) v := rfl

open scoped Classical in

theorem prod_localUnit_apply (T : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (((∏ v ∈ T, localUnit (𝓞 K) K v (t v) : (𝔸Kf)ˣ) : 𝔸Kf) w) =
      if w ∈ T then ((t w : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, fad_one_apply, if_neg (Finset.notMem_empty w)]
  | insert v T hvT ih =>
      rw [Finset.prod_insert hvT, Units.val_mul, fad_mul_apply, ih]
      by_cases hw : w = v
      · subst hw
        rw [localUnit_apply_self, if_neg hvT, if_pos (Finset.mem_insert_self _ _), mul_one]
      · rw [localUnit_apply_of_ne (𝓞 K) K v _ hw, one_mul]
        by_cases hwT : w ∈ T
        · rw [if_pos hwT, if_pos (Finset.mem_insert_of_mem hwT)]
        · rw [if_neg hwT, if_neg (by simp [hw, hwT])]

variable {K}

theorem idealMultiplicity_eq_zero_of_not_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) : idealMultiplicity K v 𝔣 = 0 := by
  classical
  unfold idealMultiplicity
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp h)

theorem idealMultiplicity_ne_zero_of_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔣) : idealMultiplicity K v 𝔣 ≠ 0 := by
  classical
  unfold idealMultiplicity
  exact (Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mpr hv

theorem apply_finUnit_localUnit_eq_one_of_valued_eq_one {η : (𝔸K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)}
    (h𝔣 : 𝔣 ≠ ⊥) (hmod : AdmitsModulus K η 𝔣) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔣) (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    η (finUnit K (localUnit (𝓞 K) K v t)) = 1 := by
  classical
  apply hmod
  · rfl
  · intro w
    show Valued.v (((localUnit (𝓞 K) K v t : (𝔸Kf)ˣ) : 𝔸Kf) w) = 1 ∧
      Valued.v (((localUnit (𝓞 K) K v t : (𝔸Kf)ˣ) : 𝔸Kf) w - 1) ≤
        WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, idealMultiplicity_eq_zero_of_not_dvd h𝔣 hv]
      refine ⟨ht, ?_⟩
      simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
      calc Valued.v ((t : w.adicCompletion K) - 1)
          ≤ max (Valued.v (t : w.adicCompletion K)) (Valued.v (1 : w.adicCompletion K)) :=
            Valuation.map_sub _ _ _
        _ = 1 := by rw [ht, map_one, max_self]
    · rw [localUnit_apply_of_ne (𝓞 K) K v t hw]
      refine ⟨map_one _, ?_⟩
      rw [sub_self, map_zero]
      exact zero_le'

theorem apply_finUnit_eq_finprod {η : (𝔸K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : AdmitsModulus K η 𝔣) {ψ : HeightOneSpectrum (𝓞 K) → ℂˣ}
    (hval : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → η (uniformizerIdele K v) = ψ v)
    (y : (𝔸Kf)ˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((y : 𝔸Kf) v) = 1 ∧
      Valued.v ((y : 𝔸Kf) v - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    η (finUnit K y) = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ψ v ^ placeOrd K y v := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 K)), T = (finite_support_placeOrd K y).toFinset :=
    ⟨_, rfl⟩
  have hmemT : ∀ v, v ∈ T ↔ placeOrd K y v ≠ 0 := fun v => by
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support]

  have hTnd : ∀ v ∈ T, ¬ v.asIdeal ∣ 𝔣 := fun v hv hdvd =>
    (hmemT v).mp hv ((placeOrd_eq_zero_iff K y v).mpr (hy v hdvd).1)

  obtain ⟨P, hP⟩ : ∃ P : (𝔸Kf)ˣ, P = ∏ v ∈ T, localUnit (𝓞 K) K v (compUnit K y v) := ⟨_, rfl⟩
  have hPapply : ∀ w, ((P : (𝔸Kf)ˣ) : 𝔸Kf) w = if w ∈ T then (y : 𝔸Kf) w else 1 := fun w => by
    rw [hP]
    exact prod_localUnit_apply K T (fun v => compUnit K y v) w
  obtain ⟨z, hz⟩ : ∃ z : (𝔸Kf)ˣ, z = y * P⁻¹ := ⟨_, rfl⟩
  have hy0 : ∀ w, (y : 𝔸Kf) w ≠ 0 := fun w h =>
    valued_ne_zero_of_unit K y w (by rw [h, map_zero])
  have hzapply : ∀ w, ((z : (𝔸Kf)ˣ) : 𝔸Kf) w = if w ∈ T then 1 else (y : 𝔸Kf) w := fun w => by
    rw [hz, Units.val_mul, fad_mul_apply, fad_units_inv_apply, hPapply]
    split_ifs with hw
    · exact mul_inv_cancel₀ (hy0 w)
    · rw [inv_one, mul_one]

  have hzval : ∀ w, Valued.v (((z : (𝔸Kf)ˣ) : 𝔸Kf) w) = 1 := fun w => by
    rw [hzapply]
    split_ifs with hw
    · exact map_one _
    · exact (placeOrd_eq_zero_iff K y w).mp (not_not.mp ((hmemT w).not.mp hw))
  have hηz : η (finUnit K z) = 1 := by
    apply hmod
    · rfl
    · intro w
      refine ⟨hzval w, ?_⟩
      show Valued.v (((z : (𝔸Kf)ˣ) : 𝔸Kf) w - 1) ≤ _
      by_cases hw : w ∈ T
      · rw [hzapply, if_pos hw, sub_self, map_zero]; exact zero_le'
      · by_cases hdvd : w.asIdeal ∣ 𝔣
        · rw [hzapply, if_neg hw]; exact (hy w hdvd).2
        · rw [idealMultiplicity_eq_zero_of_not_dvd h𝔣 hdvd]
          simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
          calc Valued.v (((z : (𝔸Kf)ˣ) : 𝔸Kf) w - 1)
              ≤ max (Valued.v (((z : (𝔸Kf)ˣ) : 𝔸Kf) w)) (Valued.v (1 : w.adicCompletion K)) :=
                Valuation.map_sub _ _ _
            _ = 1 := by rw [hzval w, map_one, max_self]

  have hfactor : ∀ v ∈ T, η (finUnit K (localUnit (𝓞 K) K v (compUnit K y v))) =
      ψ v ^ placeOrd K y v := by
    intro v hv
    have hvnd := hTnd v hv

    have hyv : Valued.v ((y : 𝔸Kf) v) = WithZero.exp (-placeOrd K y v) := by
      rw [placeOrd, neg_neg, WithZero.exp_log (valued_ne_zero_of_unit K y v)]
    have hval_t : Valued.v ((compUnit K y v * uniformizerUnit K v ^ (-placeOrd K y v) :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [Units.val_mul, map_mul, compUnit_val, hyv, Units.val_zpow_eq_zpow_val, map_zpow₀,
        valued_uniformizerUnit, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul, mul_neg,
        mul_one, neg_neg, neg_add_cancel, WithZero.exp_zero]
    have hdecomp : compUnit K y v = uniformizerUnit K v ^ placeOrd K y v *
        (compUnit K y v * uniformizerUnit K v ^ (-placeOrd K y v)) := by
      rw [mul_left_comm, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

    have hcomp : ∀ s : (v.adicCompletion K)ˣ, finUnit K (localUnit (𝓞 K) K v s) =
        ((finUnit K).comp (localUnit (𝓞 K) K v)) s := fun s => rfl
    rw [hdecomp, map_mul, map_mul, map_mul,
      apply_finUnit_localUnit_eq_one_of_valued_eq_one h𝔣 hmod hvnd _ hval_t, mul_one, hcomp,
      map_zpow, map_zpow, ← hval v hvnd]
    rfl

  have hy_eq : y = P * z := by rw [hz, mul_comm y, mul_inv_cancel_left]
  calc η (finUnit K y) = η (finUnit K P) * η (finUnit K z) := by
        rw [hy_eq, map_mul, map_mul]
    _ = η (finUnit K P) := by rw [hηz, mul_one]
    _ = ∏ v ∈ T, η (finUnit K (localUnit (𝓞 K) K v (compUnit K y v))) := by
        rw [hP, map_prod, map_prod]
    _ = ∏ v ∈ T, ψ v ^ placeOrd K y v := Finset.prod_congr rfl hfactor
    _ = ∏ᶠ v, ψ v ^ placeOrd K y v := by
        refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_).symm
        rw [Function.mem_mulSupport] at hv
        rw [Finset.mem_coe, hmemT]
        intro h0
        exact hv (by rw [h0, zpow_zero])

variable (K)

omit [NumberField K] in

theorem placeOf_injective : Function.Injective (placeOf K) := by
  intro τ τ' h
  unfold placeOf at h
  rw [InfinitePlace.mk_eq_iff] at h
  have hC : Complex.ofRealHom.comp τ = Complex.ofRealHom.comp τ' := by
    rcases h with h | h
    · exact h
    · rw [← h]
      exact (ComplexEmbedding.isReal_iff.mp (isReal_compOfRealHom K τ)).symm
  ext x
  exact Complex.ofReal_injective (RingHom.congr_fun hC x)

def signIdele (τ : K →+* ℝ) : (𝔸K)ˣ := archUnitHom (placeOf K τ) (-1)

theorem signIdele_val_snd (τ : K →+* ℝ) : ((signIdele K τ : (𝔸K)ˣ) : 𝔸K).2 = 1 := rfl

open scoped Classical in
theorem signIdele_val_fst (τ : K →+* ℝ) :
    ((signIdele K τ : (𝔸K)ˣ) : 𝔸K).1 =
      Function.update (1 : InfiniteAdeleRing K) (placeOf K τ) (-1 : (placeOf K τ).Completion) := by
  show Function.update (1 : InfiniteAdeleRing K) (placeOf K τ)
      (((-1 : ((placeOf K τ).Completion)ˣ) : (placeOf K τ).Completion)) = _
  rw [Units.val_neg, Units.val_one]

theorem signIdele_mul_self (τ : K →+* ℝ) : signIdele K τ * signIdele K τ = 1 := by
  unfold signIdele
  rw [← map_mul, neg_mul_neg, one_mul, map_one]

theorem signIdele_inv (τ : K →+* ℝ) : (signIdele K τ)⁻¹ = signIdele K τ :=
  inv_eq_of_mul_eq_one_right (signIdele_mul_self K τ)

open scoped Classical in
open _root_.NumberField.InfinitePlace.Completion in
theorem archRealProjTau_signIdele_self (τ : K →+* ℝ) :
    archRealProjTau K τ (signIdele K τ) = -1 := by
  unfold archRealProjTau
  rw [signIdele_val_fst, Function.update_self, map_neg, map_one]

open scoped Classical in
open _root_.NumberField.InfinitePlace.Completion in
theorem archRealProjTau_signIdele_of_ne {τ τ' : K →+* ℝ} (h : τ' ≠ τ) :
    archRealProjTau K τ' (signIdele K τ) = 1 := by
  unfold archRealProjTau
  rw [signIdele_val_fst, Function.update_of_ne (fun h' => h (placeOf_injective K h'))]
  exact map_one _

theorem archLocalChar_placeOf_neg_one (η : (𝔸K)ˣ →* ℂˣ) (τ : K →+* ℝ) :
    archLocalChar η (placeOf K τ) (-1) = η (signIdele K τ) := rfl

def princ (β : 𝓞 K) (hβ : β ≠ 0) : (𝔸K)ˣ :=
  Units.map (algebraMap K (𝔸K) : K →* 𝔸K)
    (Units.mk0 (algebraMap (𝓞 K) K β) (RingOfIntegers.coe_ne_zero_iff.mpr hβ))

theorem princ_val (β : 𝓞 K) (hβ : β ≠ 0) :
    ((princ K β hβ : (𝔸K)ˣ) : 𝔸K) = algebraMap K (𝔸K) (algebraMap (𝓞 K) K β) := rfl

theorem projFin_princ_apply (β : 𝓞 K) (hβ : β ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    ((projFin K (princ K β hβ) : (𝔸Kf)ˣ) : 𝔸Kf) v =
      ((algebraMap (𝓞 K) K β : K) : v.adicCompletion K) := rfl

variable {K}

theorem valued_princ_of_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : 𝓞 K} (hβ : β ≠ 0)
    (hβ1 : β - 1 ∈ 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔣) :
    Valued.v (((projFin K (princ K β hβ) : (𝔸Kf)ˣ) : 𝔸Kf) v) = 1 ∧
    Valued.v (((projFin K (princ K β hβ) : (𝔸Kf)ˣ) : 𝔸Kf) v - 1) ≤
      WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  have hle := (mem_iff_forall_valued_algebraMap_finiteAdeleRing_le K 𝔣 h𝔣 (β - 1)).mp hβ1 v hv
  have hsub : (algebraMap K (𝔸Kf) ((β - 1 : 𝓞 K) : K)) v =
      ((projFin K (princ K β hβ) : (𝔸Kf)ˣ) : 𝔸Kf) v - 1 := by
    rw [projFin_princ_apply, RingOfIntegers.coe_eq_algebraMap, map_sub, map_one, map_sub, map_one]
    rfl
  rw [hsub] at hle
  refine ⟨?_, hle⟩
  have hlt : Valued.v (((projFin K (princ K β hβ) : (𝔸Kf)ˣ) : 𝔸Kf) v - 1) < 1 := by
    refine lt_of_le_of_lt hle ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp, neg_lt_zero]
    have := idealMultiplicity_ne_zero_of_dvd h𝔣 hv
    unfold idealMultiplicity at this
    omega
  have := Valuation.map_one_add_of_lt (v := (Valued.v : Valuation (v.adicCompletion K) _)) hlt
  rwa [add_sub_cancel] at this

theorem apply_finUnit_projFin_princ {η : (𝔸K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : AdmitsModulus K η 𝔣) {ψ : HeightOneSpectrum (𝓞 K) → ℂˣ}
    (hval : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → η (uniformizerIdele K v) = ψ v)
    {β : 𝓞 K} (hβ : β ≠ 0) (hβ1 : β - 1 ∈ 𝔣) :
    η (finUnit K (projFin K (princ K β hβ))) =
      raySymbol K ψ ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
  rw [apply_finUnit_eq_finprod h𝔣 hmod hval _ (fun v hv => valued_princ_of_dvd h𝔣 hβ hβ1 hv),
    ← raySymbolUnitsHom_fadContentHom K ψ]
  show raySymbol K ψ _ = _
  congr 1
  rw [FractionalIdeal.coeIdeal_span_singleton]
  exact coe_fadContentHom_projFin_unitsMap_algebraMap K _

theorem raySymbol_eq_of_sign {𝔣 : Ideal (𝓞 K)} {ψ : HeightOneSpectrum (𝓞 K) → ℂˣ}
    {ε : (K →+* ℝ) → ℂˣ}
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
        ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), ε τ)
    {β : 𝓞 K} (hβ : β ≠ 0) (hβ1 : β - 1 ∈ 𝔣) {τ : K →+* ℝ}
    (hsgn : ∀ τ' : K →+* ℝ, 0 < τ' (β : K) ↔ τ' ≠ τ) :
    raySymbol K ψ ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = ε τ := by
  classical
  rw [hψ β hβ hβ1]
  have hfilter : Finset.univ.filter (fun τ' : K →+* ℝ => τ' (algebraMap (𝓞 K) K β) < 0) = {τ} := by
    ext τ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    have hne : τ' (algebraMap (𝓞 K) K β) ≠ 0 :=
      (map_ne_zero τ').mpr (RingOfIntegers.coe_ne_zero_iff.mpr hβ)
    constructor
    · intro hlt
      by_contra hτ
      exact (lt_asymm hlt) ((hsgn τ').mpr hτ)
    · rintro rfl
      rcases hne.lt_or_gt with h | h
      · exact h
      · exact absurd rfl ((hsgn τ').mp h)
  rw [hfilter, Finset.prod_singleton]

theorem raySymbol_sq_eq_one {𝔣 : Ideal (𝓞 K)} {ψ : HeightOneSpectrum (𝓞 K) → ℂˣ}
    {ε : (K →+* ℝ) → ℂˣ}
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
        ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), ε τ)
    {β : 𝓞 K} (hβ : β ≠ 0) (hβ1 : β - 1 ∈ 𝔣) :
    raySymbol K ψ ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ^ 2 = 1 := by
  classical
  have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  have hβ21 : β ^ 2 - 1 ∈ 𝔣 := by
    have : β ^ 2 - 1 = (β - 1) * (β + 1) := by ring
    rw [this]
    exact Ideal.mul_mem_right _ _ hβ1
  have h := hψ (β ^ 2) hβ2 hβ21
  have hfilter : Finset.univ.filter (fun τ' : K →+* ℝ => τ' (algebraMap (𝓞 K) K (β ^ 2)) < 0) = ∅ := by
    ext τ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt,
      map_pow]
    positivity
  rw [hfilter, Finset.prod_empty] at h
  have hspan : ((Ideal.span {β ^ 2} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) *
        ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
    rw [← FractionalIdeal.coeIdeal_mul, Ideal.span_singleton_mul_span_singleton, sq]
  have hne : ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
    exact hβ
  rw [hspan, raySymbol_mul K ψ hne hne] at h
  rw [sq, h]

theorem apply_signIdele_eq {η : (𝔸K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hicc : IsIdeleClassChar (𝓞 K) K η) (hfin : IsOfFinOrder η) (hmod : AdmitsModulus K η 𝔣)
    {ψ : HeightOneSpectrum (𝓞 K) → ℂˣ}
    (hval : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → η (uniformizerIdele K v) = ψ v)
    {ε : (K →+* ℝ) → ℂˣ}
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
        ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), ε τ)
    (τ : K →+* ℝ) :
    η (signIdele K τ) = ε τ := by
  classical

  obtain ⟨β, hβ0, hβ1, hβsgn⟩ :=
    HeckeCharacter.exists_ne_zero_sub_one_mem_forall_pos_iff K 𝔣 h𝔣 (fun τ' => τ' ≠ τ)

  have hP : η (princ K β hβ0) = 1 := hicc _
  have hPf : η (finUnit K (projFin K (princ K β hβ0))) = ε τ := by
    rw [apply_finUnit_projFin_princ h𝔣 hmod hval hβ0 hβ1]
    exact raySymbol_eq_of_sign hψ hβ0 hβ1 hβsgn
  have hε2 : ε τ ^ 2 = 1 := by
    rw [← raySymbol_eq_of_sign hψ hβ0 hβ1 hβsgn]
    exact raySymbol_sq_eq_one hψ hβ0 hβ1

  have hQfin : (((signIdele K τ * princ K β hβ0 * (finUnit K (projFin K (princ K β hβ0)))⁻¹ :
      (𝔸K)ˣ) : 𝔸K)).2 = 1 := by
    rw [← projFin_val, map_mul, map_mul, map_inv, projFin_finUnit, mul_inv_cancel_right]
    show ((signIdele K τ : (𝔸K)ˣ) : 𝔸K).2 = 1
    exact signIdele_val_snd K τ
  have hQpos : ∀ τ' : K →+* ℝ,
      archSign K τ' (signIdele K τ * princ K β hβ0 * (finUnit K (projFin K (princ K β hβ0)))⁻¹) := by
    intro τ'
    have hPf1 : archSign K τ' (finUnit K (projFin K (princ K β hβ0)))⁻¹ :=
      archSign_of_fst_eq_one K τ' rfl
    rw [archSign_mul, archSign_mul, iff_true_intro hPf1, iff_true]
    unfold archSign
    rw [princ, archRealProjTau_unitsMap_algebraMap]
    show 0 < archRealProjTau K τ' (signIdele K τ) ↔ 0 < τ' (algebraMap (𝓞 K) K β)
    by_cases hτ : τ' = τ
    · subst hτ
      rw [archRealProjTau_signIdele_self]
      have hnot : ¬ 0 < τ' (algebraMap (𝓞 K) K β) := fun h => (hβsgn τ').mp h rfl
      exact iff_of_false (by norm_num) hnot
    · rw [archRealProjTau_signIdele_of_ne K hτ]
      exact iff_of_true one_pos ((hβsgn τ').mpr hτ)
  have hQ : η (signIdele K τ * princ K β hβ0 * (finUnit K (projFin K (princ K β hβ0)))⁻¹) = 1 :=
    HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign K η hfin _ hQfin hQpos

  rw [map_mul, map_mul, map_inv, hP, hPf, mul_one] at hQ

  have h1 : η (signIdele K τ) = ε τ := by
    have := hQ
    rw [mul_inv_eq_one] at this
    exact this
  exact h1

end RayClassSignHeckeCharSol
p2m_reactivate "P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod.RayClassSignHeckeCharSol"

end
p2m_reactivate "P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod.RayClassSignHeckeCharSol"

open RayClassSignHeckeCharSol NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Deep.NTSupply LanglandsTunnell.P2.Artin in

theorem solution
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (ψ : HeightOneSpectrum (𝓞 K) → ℂˣ) (ε : (K →+* ℝ) → ℂˣ)
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
        ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), ε τ) :
    ∃ ξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsFiniteOrderHeckeChar K ξ ∧ AdmitsModulus K ξ 𝔣 ∧ IsUnitaryChar (𝓞 K) K ξ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ξ (uniformizerIdele K v) = ψ v) ∧
      (∀ τ : K →+* ℝ,
        archLocalChar ξ (InfinitePlace.mk (Complex.ofRealHom.comp τ)) (-1) = ε τ) := by
  classical

  have hkill : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
    intro α h0 h1 hpos
    rw [hψ α h0 h1]
    refine Finset.prod_eq_one fun τ hτ => ?_
    exact absurd (Finset.mem_filter.mp hτ).2 (not_lt.mpr (hpos τ).le)

  obtain ⟨η, hfo, hmod, huni, hval⟩ :=
    LT.HeckeChar.exists_heckeCharOfRayClassChar K 𝔣 (raySymbolDescend K ψ hkill)
  have hval' : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → η (uniformizerIdele K v) = ψ v :=
    fun v hv => by rw [hval v hv, raySymbolDescend_primeClass]
  refine ⟨η, hfo, hmod, huni, hval', fun τ => ?_⟩
  exact apply_signIdele_eq h𝔣 hfo.isIdeleClassChar hfo.isOfFinOrder hmod hval' hψ τ

end S_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
end P2MW
export P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod (solution)
