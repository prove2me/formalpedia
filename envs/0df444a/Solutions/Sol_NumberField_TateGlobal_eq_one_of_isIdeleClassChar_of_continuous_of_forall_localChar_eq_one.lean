-- Prove2me | solution 1 for NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/89526d7d-ef3b-513f-9ea4-a2a0b0f48f70

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdeleRing IsDedekindDomain
open AutomorphicForm Filter
open scoped Topology

namespace Ws22
namespace C6

variable (F : Type) [Field F] [NumberField F]

theorem fst_mul' (x y : AdeleRing (𝓞 F) F) : (x * y).1 = x.1 * y.1 := rfl
theorem snd_apply_mul' (x y : AdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)) :
    (x * y).2 w = x.2 w * y.2 w := rfl
theorem fst_one' : (1 : AdeleRing (𝓞 F) F).1 = 1 := rfl
theorem snd_apply_one' (w : HeightOneSpectrum (𝓞 F)) : (1 : AdeleRing (𝓞 F) F).2 w = 1 := rfl

theorem fst_apply_mul_unitsInv' (z : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (z : AdeleRing (𝓞 F) F).1 w * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have : ((z * z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by rw [mul_inv_cancel]; rfl
  rwa [Units.val_mul, fst_mul'] at this
theorem fst_apply_unitsInv_mul' (z : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * (z : AdeleRing (𝓞 F) F).1 w = 1 := by
  rw [mul_comm]; exact fst_apply_mul_unitsInv' F z w
theorem snd_apply_mul_unitsInv' (z : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    (z : AdeleRing (𝓞 F) F).2 w * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [← snd_apply_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, snd_apply_one']
theorem snd_apply_unitsInv_mul' (z : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w * (z : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [← snd_apply_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, snd_apply_one']
theorem fst_unitsInv' (z : (AdeleRing (𝓞 F) F)ˣ) (hz : (z : AdeleRing (𝓞 F) F).1 = 1) :
    ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  have : (z : AdeleRing (𝓞 F) F).1 * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
    rw [← fst_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, fst_one']
  rw [hz, one_mul] at this
  exact this

noncomputable def supportedProd (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ v ∈ T, Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (t v))

theorem supportedProd_fst (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((supportedProd F t T : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert v T hv ih =>
    rw [supportedProd, Finset.prod_insert hv, Units.val_mul, fst_mul']
    rw [supportedProd] at ih
    rw [ih, mul_one]
    rfl

open scoped Classical in
theorem supportedProd_snd (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    ((supportedProd F t T : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w =
      if w ∈ T then (t w : w.adicCompletion F) else 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert v T hv ih =>
    rw [supportedProd, Finset.prod_insert hv, Units.val_mul, snd_apply_mul']
    rw [supportedProd] at ih
    have hcomp : (((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (t v)) : (AdeleRing (𝓞 F) F)ˣ) :
        AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w =
          ((localUnit (𝓞 F) F v (t v) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w := rfl
    rw [ih, hcomp]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      simp [hv]
    · rw [localUnit_apply_of_ne (𝓞 F) F v (t v) hw, one_mul]
      simp [Finset.mem_insert, hw]

theorem apply_supportedProd (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ v ∈ T, localChar χ v = 1) :
    χ (supportedProd F t T) = 1 := by
  rw [supportedProd, map_prod]
  refine Finset.prod_eq_one fun v hv => ?_
  have h : localChar χ v (t v) = 1 := by rw [hT v hv]; rfl
  rw [localChar_apply] at h
  exact h

theorem apply_eq_one_of_fst_eq_one (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, localChar χ v = 1)
    (x : (AdeleRing (𝓞 F) F)ˣ) (hx1 : (x : AdeleRing (𝓞 F) F).1 = 1)
    (hxS : ∀ v ∈ S, (x : AdeleRing (𝓞 F) F).2 v = 1) : χ x = 1 := by
  classical
  have hS' : ∀ v ∉ S, IsUnramifiedCharAt χ v := fun v hv t _ _ => by rw [hS v hv]; rfl

  have hfin : {w : HeightOneSpectrum (𝓞 F) | ¬ ((x : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F ∧
      ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F)}.Finite := by
    have h := ((x : AdeleRing (𝓞 F) F).2).2.and (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
    exact Filter.eventually_cofinite.1 h
  let T : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
  have hTmem : ∀ w, w ∈ T ↔ ¬ ((x : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F ∧
      ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F) := fun w => by
    rw [Set.Finite.mem_toFinset]; rfl

  have hSinv : ∀ v ∈ S, ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro v hv
    have h := snd_apply_mul_unitsInv' F x v
    rwa [hxS v hv, one_mul] at h
  have hTS : ∀ v ∈ T, v ∉ S := by
    intro v hv hvS
    rw [hTmem] at hv
    exact hv ⟨by rw [hxS v hvS]; exact one_mem _, by rw [hSinv v hvS]; exact one_mem _⟩

  let t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ := fun v => finiteUnitsComponent (𝓞 F) F v x
  have ht : ∀ v, (t v : v.adicCompletion F) = (x : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  let p := supportedProd F t T
  have hp : χ p = 1 := apply_supportedProd F χ t T fun v hv => hS v (hTS v hv)

  let q : (AdeleRing (𝓞 F) F)ˣ := x * p⁻¹
  have hq1 : (q : AdeleRing (𝓞 F) F).1 = 1 := by
    show ((x * p⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1
    rw [Units.val_mul, fst_mul', hx1, one_mul]
    exact fst_unitsInv' F p (supportedProd_fst F t T)
  have hq2 : ∀ w, (q : AdeleRing (𝓞 F) F).2 w = if w ∈ T then 1 else (x : AdeleRing (𝓞 F) F).2 w := by
    intro w
    have hpw := supportedProd_snd F t T w
    have hpinv := snd_apply_unitsInv_mul' F p w
    show ((x * p⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = _
    rw [Units.val_mul, snd_apply_mul']
    by_cases hw : w ∈ T
    · rw [if_pos hw]
      rw [hpw, if_pos hw, ht] at hpinv
      rw [mul_comm] at hpinv
      exact hpinv
    · rw [if_neg hw]
      rw [hpw, if_neg hw, mul_one] at hpinv
      rw [hpinv, mul_one]
  have hqS : ∀ v ∈ S, (q : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro v hv
    rw [hq2]
    split_ifs
    · rfl
    · exact hxS v hv
  have hqint : ∀ w, (q : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F := by
    intro w
    rw [hq2]
    by_cases hw : w ∈ T
    · rw [if_pos hw]; exact one_mem _
    · rw [if_neg hw]
      have := (hTmem w).not.1 hw
      push_neg at this
      exact this.1
  have hqinvint : ∀ w, ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F := by
    intro w
    have hmul := snd_apply_mul_unitsInv' F q w
    by_cases hw : w ∈ T
    · have h1 : (q : AdeleRing (𝓞 F) F).2 w = 1 := by rw [hq2, if_pos hw]
      rw [h1, one_mul] at hmul
      rw [hmul]; exact one_mem _
    · have h1 : (q : AdeleRing (𝓞 F) F).2 w = (x : AdeleRing (𝓞 F) F).2 w := by rw [hq2, if_neg hw]
      rw [h1] at hmul
      have hmul' := snd_apply_mul_unitsInv' F x w
      have hx0 : (x : AdeleRing (𝓞 F) F).2 w ≠ 0 := fun h0 => by
        rw [h0, zero_mul] at hmul; exact zero_ne_one hmul
      have : ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w :=
        mul_left_cancel₀ hx0 (hmul.trans hmul'.symm)
      rw [this]
      have := (hTmem w).not.1 hw
      push_neg at this
      exact this.2
  have hq3 : finitePartUnits (𝓞 F) F q ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F := by
    refine ⟨fun w => hqint w, fun w => ?_⟩
    rw [← map_inv]
    exact hqinvint w
  have hq : χ q = 1 :=
    NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous F χ hcont S hS' q hq1 hqS hq3
  have hx : x = q * p := by
    show x = x * p⁻¹ * p
    rw [inv_mul_cancel_right]
  rw [hx, map_mul, hq, hp, one_mul]

abbrev Mixed (S : Finset (HeightOneSpectrum (𝓞 F))) : Type _ :=
  InfiniteAdeleRing F × ((v : ↥S) → v.1.adicCompletion F)

noncomputable def mixedHom (S : Finset (HeightOneSpectrum (𝓞 F))) : F →+* Mixed F S :=
  RingHom.prod (algebraMap F (InfiniteAdeleRing F)) (RingHom.pi fun v : ↥S => algebraMap F (v.1.adicCompletion F))

theorem mixedHom_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (k : F) :
    mixedHom F S k = (algebraMap F (InfiniteAdeleRing F) k, fun v : ↥S => algebraMap F (v.1.adicCompletion F) k) :=
  rfl

theorem denseRange_mixedHom (S : Finset (HeightOneSpectrum (𝓞 F))) : DenseRange (mixedHom F S) :=
  NumberField.denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion F S

theorem cofinite_le_principal_compl (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite

noncomputable def finExtPrincipal (S : Finset (HeightOneSpectrum (𝓞 F))) (b : (v : ↥S) → v.1.adicCompletion F) :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) := by
  classical
  exact ⟨fun v => if h : v ∈ S then b ⟨v, h⟩ else 1,
    Filter.eventually_principal.2 fun v hv => by
      have hv' : v ∉ S := fun h => hv h
      simp only [dif_neg hv']
      exact one_mem _⟩

open scoped Classical in
noncomputable def finExt (S : Finset (HeightOneSpectrum (𝓞 F))) (b : (v : ↥S) → v.1.adicCompletion F) :
    FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl F S) (finExtPrincipal F S b)

open scoped Classical in
theorem finExt_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (b : (v : ↥S) → v.1.adicCompletion F)
    (v : HeightOneSpectrum (𝓞 F)) :
    finExt F S b v = if h : v ∈ S then b ⟨v, h⟩ else 1 := rfl

open scoped Classical in
theorem continuous_finExt (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (finExt F S) := by
  refine (RestrictedProduct.continuous_inclusion (cofinite_le_principal_compl F S)).comp ?_
  rw [RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff]
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · refine Continuous.congr (continuous_apply (⟨v, h⟩ : ↥S)) fun b => ?_
    show b ⟨v, h⟩ = (if h : v ∈ S then b ⟨v, h⟩ else 1)
    rw [dif_pos h]
  · refine Continuous.congr (continuous_const (y := (1 : v.adicCompletion F))) fun b => ?_
    show (1 : v.adicCompletion F) = (if h : v ∈ S then b ⟨v, h⟩ else 1)
    rw [dif_neg h]

noncomputable def J (S : Finset (HeightOneSpectrum (𝓞 F))) : Mixed F S →* AdeleRing (𝓞 F) F where
  toFun m := (m.1, finExt F S m.2)
  map_one' := by
    refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
    show finExt F S 1 v = (1 : FiniteAdeleRing (𝓞 F) F) v
    rw [finExt_apply]
    split_ifs <;> rfl
  map_mul' m n := by
    refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
    show finExt F S (m.2 * n.2) v = (finExt F S m.2 * finExt F S n.2) v
    rw [show (finExt F S m.2 * finExt F S n.2) v = finExt F S m.2 v * finExt F S n.2 v from rfl,
      finExt_apply, finExt_apply, finExt_apply]
    split_ifs
    · rfl
    · exact (mul_one _).symm

theorem J_fst (S : Finset (HeightOneSpectrum (𝓞 F))) (m : Mixed F S) : (J F S m).1 = m.1 := rfl

open scoped Classical in
theorem J_snd_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (m : Mixed F S) (v : HeightOneSpectrum (𝓞 F)) :
    (J F S m).2 v = if h : v ∈ S then m.2 ⟨v, h⟩ else 1 := rfl

theorem continuous_J (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (J F S) :=
  Continuous.prodMk continuous_fst ((continuous_finExt F S).comp continuous_snd)

private theorem _root_.Units.tendsto_of_val_of_inv {α M : Type*} [Monoid M] [TopologicalSpace M] {l : Filter α}
    {f : α → Mˣ} {u : Mˣ} (h1 : Tendsto (fun a => (f a : M)) l (𝓝 (u : M)))
    (h2 : Tendsto (fun a => (((f a)⁻¹ : Mˣ) : M)) l (𝓝 ((u⁻¹ : Mˣ) : M))) : Tendsto f l (𝓝 u) := by
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply]
  exact h1.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp h2)

p2m_alias "P2MW.S_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one.Units.tendsto_of_val_of_inv" "Units.tendsto_of_val_of_inv"
end Ws22.C6

open Ws22.C6 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hcont : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, localChar χ v = 1) :
    χ = 1 := by
  classical
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]
  have hD := apply_eq_one_of_fst_eq_one F χ hcont S hS

  let m : Mixed F S := ((x : AdeleRing (𝓞 F) F).1, fun v : ↥S => (x : AdeleRing (𝓞 F) F).2 v.1)
  let m' : Mixed F S := (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1, fun v : ↥S => ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v.1)
  have hmm' : m * m' = 1 :=
    Prod.ext (funext fun w => fst_apply_mul_unitsInv' F x w) (funext fun v => snd_apply_mul_unitsInv' F x v.1)
  have hm'm : m' * m = 1 :=
    Prod.ext (funext fun w => fst_apply_unitsInv_mul' F x w) (funext fun v => snd_apply_unitsInv_mul' F x v.1)
  let sx : (AdeleRing (𝓞 F) F)ˣ := ⟨J F S m, J F S m', by rw [← map_mul, hmm', map_one], by rw [← map_mul, hm'm, map_one]⟩

  have hy : χ (x * sx⁻¹) = 1 := by
    refine hD (x * sx⁻¹) ?_ ?_
    · show ((x : AdeleRing (𝓞 F) F) * J F S m').1 = 1
      rw [fst_mul', J_fst]
      funext w
      exact fst_apply_mul_unitsInv' F x w
    · intro v hv
      show ((x : AdeleRing (𝓞 F) F) * J F S m').2 v = 1
      rw [snd_apply_mul', J_snd_apply, dif_pos hv]
      exact snd_apply_mul_unitsInv' F x v
  have hxsx : χ x = χ sx := by
    have : x = x * sx⁻¹ * sx := by rw [inv_mul_cancel_right]
    rw [this, map_mul, hy, one_mul]
  rw [hxsx]

  let L : Filter F := Filter.comap (mixedHom F S) (𝓝 m)
  haveI hL : L.NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨y, hyt, ⟨k, rfl⟩⟩ := mem_closure_iff_nhds.1 (denseRange_mixedHom F S m) t ht
    exact ⟨k, hyt⟩
  have htend : Tendsto (mixedHom F S) L (𝓝 m) := Filter.tendsto_comap

  have hm1 : ∀ w, m.1 w ≠ 0 := fun w h0 => by
    have := fst_apply_mul_unitsInv' F x w
    rw [show (x : AdeleRing (𝓞 F) F).1 w = m.1 w from rfl, h0, zero_mul] at this
    exact zero_ne_one this
  have hm2 : ∀ v : ↥S, m.2 v ≠ 0 := fun v h0 => by
    have := snd_apply_mul_unitsInv' F x v.1
    rw [show (x : AdeleRing (𝓞 F) F).2 v.1 = m.2 v from rfl, h0, zero_mul] at this
    exact zero_ne_one this
  have hm'1 : ∀ w, m'.1 w = (m.1 w)⁻¹ := fun w =>
    eq_inv_of_mul_eq_one_right (fst_apply_mul_unitsInv' F x w)
  have hm'2 : ∀ v : ↥S, m'.2 v = (m.2 v)⁻¹ := fun v =>
    eq_inv_of_mul_eq_one_right (snd_apply_mul_unitsInv' F x v.1)

  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hne : ∀ᶠ k in L, k ≠ 0 := by
    have hU : {n : Mixed F S | n.1 w₀ ≠ 0} ∈ 𝓝 m :=
      (isOpen_ne_fun ((continuous_apply w₀).comp continuous_fst) continuous_const).mem_nhds (hm1 w₀)
    filter_upwards [htend.eventually hU] with k hk
    intro hk0
    apply hk
    show (mixedHom F S k).1 w₀ = 0
    rw [hk0, map_zero]
    rfl

  let E : F → (AdeleRing (𝓞 F) F)ˣ := fun k => if hk : k = 0 then 1 else
    ⟨J F S (mixedHom F S k), J F S (mixedHom F S k⁻¹),
      by rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk, map_one, map_one],
      by rw [← map_mul, ← map_mul, inv_mul_cancel₀ hk, map_one, map_one]⟩
  have hEval : ∀ k, k ≠ 0 → (E k : AdeleRing (𝓞 F) F) = J F S (mixedHom F S k) := fun k hk => by
    simp only [E, dif_neg hk]
  have hEinvval : ∀ k, k ≠ 0 → (((E k)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = J F S (mixedHom F S k⁻¹) :=
    fun k hk => by
      rw [← Units.inv_eq_val_inv]
      simp only [E, dif_neg hk]
  have hE : ∀ k, k ≠ 0 → χ (E k) = 1 := by
    intro k hk
    let P : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)) (Units.mk0 k hk)
    have hP : χ P = 1 := hχ (Units.mk0 k hk)
    have hPval : (P : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) k := rfl
    have hPinv : ((P⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) k⁻¹ := by
      show (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)) (Units.mk0 k hk))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = _
      rw [← map_inv, Units.coe_map]
      congr 1
    have hz : χ (P⁻¹ * E k) = 1 := by
      refine hD (P⁻¹ * E k) ?_ ?_
      · rw [Units.val_mul, fst_mul', hPinv, hEval k hk, J_fst, mixedHom_apply]
        show algebraMap F (InfiniteAdeleRing F) k⁻¹ * algebraMap F (InfiniteAdeleRing F) k = 1
        rw [← map_mul, inv_mul_cancel₀ hk, map_one]
      · intro v hv
        rw [Units.val_mul, snd_apply_mul', hPinv, hEval k hk, J_snd_apply, dif_pos hv, mixedHom_apply]
        show algebraMap F (FiniteAdeleRing (𝓞 F) F) k⁻¹ v * algebraMap F (v.adicCompletion F) k = 1
        rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
        show algebraMap F (v.adicCompletion F) k⁻¹ * algebraMap F (v.adicCompletion F) k = 1
        rw [← map_mul, inv_mul_cancel₀ hk, map_one]
    have : E k = P * (P⁻¹ * E k) := by rw [mul_inv_cancel_left]
    rw [this, map_mul, hP, hz, one_mul]

  have hinv : Tendsto (fun k => mixedHom F S k⁻¹) L (𝓝 m') := by
    have e : (fun k => mixedHom F S k⁻¹) = fun k => ((fun w => ((mixedHom F S k).1 w)⁻¹), fun v => ((mixedHom F S k).2 v)⁻¹) := by
      funext k
      refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
      · show algebraMap F (w.Completion) k⁻¹ = (algebraMap F (w.Completion) k)⁻¹
        exact map_inv₀ _ _
      · show algebraMap F (v.1.adicCompletion F) k⁻¹ = (algebraMap F (v.1.adicCompletion F) k)⁻¹
        exact map_inv₀ _ _
    have em' : m' = ((fun w => (m.1 w)⁻¹), fun v => (m.2 v)⁻¹) := Prod.ext (funext hm'1) (funext hm'2)
    rw [e, em']
    refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 fun w => ?_) (tendsto_pi_nhds.2 fun v => ?_)
    · exact (((continuous_apply w).comp continuous_fst).tendsto m |>.comp htend).inv₀ (hm1 w)
    · exact (((continuous_apply v).comp continuous_snd).tendsto m |>.comp htend).inv₀ (hm2 v)
  have hval : Tendsto (fun k => ((sx * (E k)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) L (𝓝 ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    have h1 : Tendsto (fun k => J F S (m * mixedHom F S k⁻¹)) L (𝓝 (J F S (m * m'))) :=
      ((continuous_J F S).tendsto _).comp (tendsto_const_nhds.mul hinv)
    rw [hmm', map_one] at h1
    refine h1.congr' ?_
    filter_upwards [hne] with k hk
    rw [Units.val_mul, hEinvval k hk, map_mul]
  have hinvval : Tendsto (fun k => (((sx * (E k)⁻¹)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) L
      (𝓝 (((1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    have h1 : Tendsto (fun k => J F S (mixedHom F S k * m')) L (𝓝 (J F S (m * m'))) :=
      ((continuous_J F S).tendsto _).comp (htend.mul tendsto_const_nhds)
    rw [hmm', map_one] at h1
    rw [show (((1 : (AdeleRing (𝓞 F) F)ˣ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 1 by rw [inv_one]; rfl]
    refine h1.congr' ?_
    filter_upwards [hne] with k hk
    rw [mul_inv_rev, inv_inv, Units.val_mul, hEval k hk, map_mul]
    congr 1
  have hu : Tendsto (fun k => sx * (E k)⁻¹) L (𝓝 1) := Units.tendsto_of_val_of_inv hval hinvval

  have hχu : Tendsto (fun k => χ (sx * (E k)⁻¹)) L (𝓝 (χ 1)) := (hcont.tendsto 1).comp hu
  rw [map_one] at hχu
  have hconst : Tendsto (fun _ : F => χ sx) L (𝓝 1) := by
    refine hχu.congr' ?_
    filter_upwards [hne] with k hk
    rw [map_mul, map_inv, hE k hk, inv_one, mul_one]
  exact tendsto_const_nhds_iff.1 hconst

end S_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
end P2MW
export P2MW.S_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one (solution)
