-- Prove2me | solution 1 for M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9b52c8ae-2331-50af-a168-53e3b7ee26fc

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_FiniteConorm
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits
import Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits
import Theorems.Thm_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv
import Theorems.Thm_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1
import Theorems.Thm_NumberField_PlaceDecomp_card_over_mul_card_decomp_above
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain

namespace P2mS26GL

attribute [local instance 2000] Rep.hV2 Rep.hV1

open NumberField IsDedekindDomain NumberField.PlaceTransport
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Fib (v : HeightOneSpectrum (𝓞 K)) : Type := {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}

theorem fib_cofinite (v : HeightOneSpectrum (𝓞 K)) : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, w.under (𝓞 K) ≠ v :=
  (M4aHerbrand.Bridge.tendsto_under_cofinite (𝓞 K) K L (𝓞 L)).eventually (Filter.eventually_cofinite_ne v)

theorem act_coord (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L)
    {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w') : (D.act σ x).2 w' = transport σ h (x.2 w) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  rw [Subsingleton.elim D (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x h

variable {K L}

theorem inv_smul_mem (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 K)} (w : Fib K L v) : (σ⁻¹ • w.1).under (𝓞 K) = v :=
  (NumberField.PlaceTransport.under_smul K L σ⁻¹ w.1).trans w.2

noncomputable def sh (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 K)} (w : Fib K L v) : Fib K L v := ⟨σ⁻¹ • w.1, inv_smul_mem σ w⟩

theorem smul_sh (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 K)} (w : Fib K L v) : σ • (sh σ w).1 = w.1 := smul_inv_smul σ w.1

section ext
variable {v : HeightOneSpectrum (𝓞 K)}

open Classical in

noncomputable def ext1 (u : Π w : Fib K L v, w.1.adicCompletion L) : FiniteAdeleRing (𝓞 L) L :=
  ⟨fun w => if h : w.under (𝓞 K) = v then u ⟨w, h⟩ else 1,
    (fib_cofinite K L v).mono fun w hw => by
      simp only [dif_neg hw]
      exact one_mem _⟩

open Classical in
theorem ext1_apply (u : Π w : Fib K L v, w.1.adicCompletion L) (w : Fib K L v) : ext1 u w.1 = u w := by
  obtain ⟨w, rfl⟩ := w
  show (if h : w.under (𝓞 K) = w.under (𝓞 K) then u ⟨w, h⟩ else 1) = u ⟨w, rfl⟩
  rw [dif_pos rfl]

end ext

section pinned
variable (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem phiF_apply
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : Fib K L v.1, x w.1 = (u : Π w : Fib K L v.1, w.1.adicCompletion L) w) →
      ∀ w : Fib K L v.1, (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = (Φf v u : Π w : Fib K L v.1, w.1.adicCompletion L) w)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (w : Fib K L v.1) :
    (Φf v u : Π w : Fib K L v.1, w.1.adicCompletion L) w
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w)) := by
  rw [← hΦf v u (ext1 (u : Π w : Fib K L v.1, w.1.adicCompletion L)) (ext1_apply _) w,
    act_coord K L D σ _ (smul_sh σ w)]
  show transport σ (smul_sh σ w) (ext1 (u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w).1) = _
  rw [ext1_apply]

theorem phiB_apply
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : Fib K L v.1, x w.1 = ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : Fib K L v.1, (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = ((Φb v u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (w : Fib K L v.1) :
    ((Φb v u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) (sh σ w) : (sh σ w).1.adicCompletion L) := by
  rw [← hΦb v u (ext1 fun w => ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) (ext1_apply _) w,
    act_coord K L D σ _ (smul_sh σ w)]
  show transport σ (smul_sh σ w) (ext1 (fun w => ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) (sh σ w).1) = _
  rw [ext1_apply]

end pinned

section ident
variable (S : Finset (HeightOneSpectrum (𝓞 K))) [IsGalois K L]

noncomputable def heartF (v : HeightOneSpectrum (𝓞 K)) :
    (Rep.coind (FiniteSIdele.D K L v).subtype (FiniteSIdele.localUnits K L v)) ≃+ Additive (Π w : Fib K L v, (w.1.adicCompletion L)ˣ) :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits K L v).choose

theorem heartF_spec (v : HeightOneSpectrum (𝓞 K)) (g : L ≃ₐ[K] L) (f) (w w' : Fib K L v) (h : g • w'.1 = w.1) :
    Additive.toMul (heartF v ((Rep.coind (FiniteSIdele.D K L v).subtype (FiniteSIdele.localUnits K L v)).ρ g f)) w
      = transportUnits g h (Additive.toMul (heartF v f) w') :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits K L v).choose_spec g f w w' h

noncomputable def heartB (v : HeightOneSpectrum (𝓞 K)) :
    (Rep.coind (FiniteSIdele.D K L v).subtype (FiniteSIdele.localIntegerUnits K L v)) ≃+ Additive (Π w : Fib K L v, (w.1.adicCompletionIntegers L)ˣ) :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits K L v).choose

theorem heartB_spec (v : HeightOneSpectrum (𝓞 K)) (g : L ≃ₐ[K] L) (f) (w w' : Fib K L v) (h : g • w'.1 = w.1) :
    Additive.toMul (heartB v ((Rep.coind (FiniteSIdele.D K L v).subtype (FiniteSIdele.localIntegerUnits K L v)).ρ g f)) w
      = transportIntegerUnits g h (Additive.toMul (heartB v f) w') :=
  (NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits K L v).choose_spec g f w w' h

abbrev XS : Type :=
  (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}, (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) ×
    (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)

noncomputable def toFibre (u : XS (K := K) (L := L) S) : (i : FiniteSIdele.Index K S) → FiniteSIdele.fibre K L S i :=
  fun i => match i with
    | Sum.inl v => (heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.1 v)))
    | Sum.inr v => (heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.2 v)))

noncomputable def ofFibre (f : (i : FiniteSIdele.Index K S) → FiniteSIdele.fibre K L S i) : XS (K := K) (L := L) S :=
  (fun v => MulEquiv.piUnits.symm (Additive.toMul (heartF v.1 (f (Sum.inl v)))),
   fun v => MulEquiv.piUnits.symm (Additive.toMul (heartB v.1 (f (Sum.inr v)))))

theorem toFibre_inl (u : XS (K := K) (L := L) S) (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) :
    toFibre S u (Sum.inl v) = (heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.1 v))) := rfl

theorem toFibre_inr (u : XS (K := K) (L := L) S) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    toFibre S u (Sum.inr v) = (heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.2 v))) := rfl

set_option maxHeartbeats 3200000 in
theorem ofFibre_toFibre (u : XS (K := K) (L := L) S) : ofFibre S (toFibre S u) = u := by
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show MulEquiv.piUnits.symm (Additive.toMul (heartF v.1 ((heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.1 v)))))) = u.1 v
    rw [AddEquiv.apply_symm_apply, toMul_ofMul, MulEquiv.symm_apply_apply]
  · show MulEquiv.piUnits.symm (Additive.toMul (heartB v.1 ((heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.2 v)))))) = u.2 v
    rw [AddEquiv.apply_symm_apply, toMul_ofMul, MulEquiv.symm_apply_apply]

set_option maxHeartbeats 3200000 in
theorem toFibre_ofFibre (f : (i : FiniteSIdele.Index K S) → FiniteSIdele.fibre K L S i) : toFibre S (ofFibre S f) = f := by
  funext i
  cases i with
  | inl v =>
    show (heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits (MulEquiv.piUnits.symm (Additive.toMul (heartF v.1 (f (Sum.inl v))))))) = f (Sum.inl v)
    rw [MulEquiv.apply_symm_apply, ofMul_toMul, AddEquiv.symm_apply_apply]
  | inr v =>
    show (heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits (MulEquiv.piUnits.symm (Additive.toMul (heartB v.1 (f (Sum.inr v))))))) = f (Sum.inr v)
    rw [MulEquiv.apply_symm_apply, ofMul_toMul, AddEquiv.symm_apply_apply]

set_option maxHeartbeats 3200000 in
theorem toFibre_mul (u u' : XS (K := K) (L := L) S) : toFibre S (u * u') = toFibre S u + toFibre S u' := by
  funext i
  cases i with
  | inl v =>
    show (heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits ((u * u').1 v))) = (heartF v.1).symm _ + (heartF v.1).symm _
    rw [Prod.fst_mul, Pi.mul_apply, map_mul, ofMul_mul, map_add]
  | inr v =>
    show (heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits ((u * u').2 v))) = (heartB v.1).symm _ + (heartB v.1).symm _
    rw [Prod.snd_mul, Pi.mul_apply, map_mul, ofMul_mul, map_add]

set_option maxHeartbeats 3200000 in

noncomputable def ident : Additive (XS (K := K) (L := L) S) ≃+ (FiniteSIdele.obj K L S) where
  toFun x := toFibre S (Additive.toMul x)
  invFun f := Additive.ofMul (ofFibre S f)
  left_inv x := by
    show Additive.ofMul (ofFibre S (toFibre S (Additive.toMul x))) = x
    rw [ofFibre_toFibre, ofMul_toMul]
  right_inv f := by
    show toFibre S (ofFibre S (Additive.toMul (Additive.ofMul f))) = f
    rw [toMul_ofMul, toFibre_ofFibre]
  map_add' x y := by
    show toFibre S (Additive.toMul (x + y)) = toFibre S (Additive.toMul x) + toFibre S (Additive.toMul y)
    rw [toMul_add, toFibre_mul]

theorem ident_apply (x : Additive (XS (K := K) (L := L) S)) : ident S x = toFibre S (Additive.toMul x) := rfl

noncomputable def phiX (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (u : XS (K := K) (L := L) S) : XS (K := K) (L := L) S :=
  (fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))

set_option maxHeartbeats 3200000 in

theorem ident_phiX (σ : L ≃ₐ[K] L)
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hF : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (w : Fib K L v.1),
      ((Φf v u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) : Π w : Fib K L v.1, w.1.adicCompletion L) w
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w)))
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hB : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (w : Fib K L v.1),
      (((Φb v u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) (sh σ w) : (sh σ w).1.adicCompletion L))
    (u : XS (K := K) (L := L) S) :
    ident S (Additive.ofMul (phiX S Φf Φb u)) = (FiniteSIdele.obj K L S).ρ σ (ident S (Additive.ofMul u)) := by
  rw [ident_apply, ident_apply, toMul_ofMul, toMul_ofMul]
  funext i
  rw [GroupCohomology.RepPi.obj_rho_apply]
  cases i with
  | inl v =>
    show (heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits ((phiX S Φf Φb u).1 v)))
      = (Rep.coind (FiniteSIdele.D K L v.1).subtype (FiniteSIdele.localUnits K L v.1)).ρ σ
          ((heartF v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.1 v))))
    apply (heartF v.1).injective
    rw [AddEquiv.apply_symm_apply]
    apply Additive.toMul.injective
    funext w
    rw [toMul_ofMul, heartF_spec v.1 σ _ w (sh σ w) (smul_sh σ w), AddEquiv.apply_symm_apply, toMul_ofMul]
    ext
    exact hF v (u.1 v) w
  | inr v =>
    show (heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits ((phiX S Φf Φb u).2 v)))
      = (Rep.coind (FiniteSIdele.D K L v.1).subtype (FiniteSIdele.localIntegerUnits K L v.1)).ρ σ
          ((heartB v.1).symm (Additive.ofMul (MulEquiv.piUnits (u.2 v))))
    apply (heartB v.1).injective
    rw [AddEquiv.apply_symm_apply]
    apply Additive.toMul.injective
    funext w
    rw [toMul_ofMul, heartB_spec v.1 σ _ w (sh σ w) (smul_sh σ w), AddEquiv.apply_symm_apply, toMul_ofMul]
    ext
    exact hB v (u.2 v) w

set_option maxHeartbeats 3200000 in

theorem ident_phiX_pow (σ : L ≃ₐ[K] L)
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hF : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (w : Fib K L v.1),
      ((Φf v u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) : Π w : Fib K L v.1, w.1.adicCompletion L) w
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w)))
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hB : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (w : Fib K L v.1),
      (((Φb v u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) (sh σ w) : (sh σ w).1.adicCompletion L))
    (i : ℕ) (u : XS (K := K) (L := L) S) :
    ident S (Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v)) : XS (K := K) (L := L) S))
      = (FiniteSIdele.obj K L S).ρ (σ ^ i) (ident S (Additive.ofMul u)) := by
  induction i with
  | zero =>
    simp only [pow_zero, MulAut.one_apply, Prod.mk.eta, map_one, Module.End.one_apply]
  | succ i ih =>
    have : ((fun v => (Φf v ^ (i + 1)) (u.1 v), fun v => (Φb v ^ (i + 1)) (u.2 v)) : XS (K := K) (L := L) S)
        = phiX S Φf Φb ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))) := by
      refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
      · show (Φf v ^ (i + 1)) (u.1 v) = Φf v ((Φf v ^ i) (u.1 v)); rw [pow_succ']; rfl
      · show (Φb v ^ (i + 1)) (u.2 v) = Φb v ((Φb v ^ i) (u.2 v)); rw [pow_succ']; rfl
    rw [this, ident_phiX S σ Φf hF Φb hB, ih, pow_succ', map_mul]
    rfl

set_option maxHeartbeats 3200000 in

theorem hd_ident (σ : L ≃ₐ[K] L)
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hF : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (w : Fib K L v.1),
      ((Φf v u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) : Π w : Fib K L v.1, w.1.adicCompletion L) w
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w)))
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hB : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (w : Fib K L v.1),
      (((Φb v u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) (sh σ w) : (sh σ w).1.adicCompletion L))
    (d : Additive (XS (K := K) (L := L) S) →+ Additive (XS (K := K) (L := L) S))
    (hd : ∀ u, d (Additive.ofMul u) = Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (x : Additive (XS (K := K) (L := L) S)) :
    ident S (d x) = (FiniteSIdele.obj K L S).ρ σ (ident S x) - ident S x := by
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
  rw [hd u]
  exact (map_sub (ident S) _ _).trans (congrArg (· - ident S (Additive.ofMul u)) (ident_phiX S σ Φf hF Φb hB u))

set_option maxHeartbeats 3200000 in

theorem hN_ident (σ : L ≃ₐ[K] L)
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hF : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (w : Fib K L v.1),
      ((Φf v u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) : Π w : Fib K L v.1, w.1.adicCompletion L) w
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w)))
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hB : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (w : Fib K L v.1),
      (((Φb v u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) (sh σ w) : (sh σ w).1.adicCompletion L))
    (n : ℕ) (N : Additive (XS (K := K) (L := L) S) →+ Additive (XS (K := K) (L := L) S))
    (hN : ∀ u, N (Additive.ofMul u) = ∑ i ∈ Finset.range n, Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))
    (x : Additive (XS (K := K) (L := L) S)) :
    ident S (N x) = ∑ i ∈ Finset.range n, (FiniteSIdele.obj K L S).ρ (σ ^ i) (ident S x) := by
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
  rw [hN u]
  exact (map_sum (ident S) _ _).trans (Finset.sum_congr rfl fun i _ => ident_phiX_pow S σ Φf hF Φb hB i u)

end ident

end P2mS26GL

set_option maxHeartbeats 3200000 in

theorem P2mS26GL.finSIdeleFibreBox_u0
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = (u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          w.1.adicCompletion L) w) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          (Φf v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            w.1.adicCompletion L) w)
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = ((u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          ((Φb v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))
    (d : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (N : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))
    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : IsCyclic (L ≃ₐ[K] L) := by
    first
    | exact ⟨⟨σ, hσ⟩⟩
    | exact ⟨⟨σ, fun τ => (Subgroup.mem_zpowers_iff.1 (hσ τ))⟩⟩

  have hF := P2mS26GL.phiF_apply σ D S Φf hΦf
  have hB := P2mS26GL.phiB_apply σ D S Φb hΦb

  have hd' := P2mS26GL.hd_ident S σ Φf hF Φb hB d hd
  have hN' := P2mS26GL.hN_ident S σ Φf hF Φb hB (Nat.card (L ≃ₐ[K] L)) N hN
  obtain ⟨h0, h1⟩ := Rep.natCard_kerModRange_eq_natCard_tate_of_addEquiv (NumberField.FiniteSIdele.obj K L S) σ hσ
    (P2mS26GL.ident S) d hd' N hN'

  have hBJ := NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1 K L S hSram
  refine ⟨?_, ?_⟩
  · rw [h0, hBJ.1]
    refine Finset.prod_congr rfl fun v _ => ?_
    have h25 := NumberField.PlaceDecomp.card_over_mul_card_decomp_above K L v
    have hpos : 0 < Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} :=
      Nat.pos_of_ne_zero fun h0 => (Nat.card_pos (α := L ≃ₐ[K] L)).ne' (by rw [← h25, h0, zero_mul])
    rw [hsf v, ← h25, Nat.mul_div_cancel_left _ hpos]
  · rw [h1]
    exact Nat.card_eq_one_iff_unique.2 ⟨hBJ.2, ⟨0⟩⟩

namespace P2mS26Univ
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

universe uK uL

section generic
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerEquiv (Θ : A ≃+ B) (d : A →+ A) (d' : B →+ B) (hd : ∀ a, Θ (d a) = d' (Θ a)) : d.ker ≃+ d'.ker where
  toFun a := ⟨Θ (a : A), by rw [AddMonoidHom.mem_ker, ← hd, (AddMonoidHom.mem_ker).1 a.2, map_zero]⟩
  invFun b := ⟨Θ.symm (b : B), by
    rw [AddMonoidHom.mem_ker, ← Θ.injective.eq_iff, hd, AddEquiv.apply_symm_apply, map_zero]
    exact b.2⟩
  left_inv a := Subtype.ext (Θ.symm_apply_apply (a : A))
  right_inv b := Subtype.ext (Θ.apply_symm_apply (b : B))
  map_add' a b := Subtype.ext (map_add Θ (a : A) (b : A))

theorem card_kerModRange_eq_of_addEquiv (Θ : A ≃+ B) (d N : A →+ A) (d' N' : B →+ B)
    (hd : ∀ a, Θ (d a) = d' (Θ a)) (hN : ∀ a, Θ (N a) = N' (Θ a)) :
    Nat.card (d.ker ⧸ N.range.addSubgroupOf d.ker) = Nat.card (d'.ker ⧸ N'.range.addSubgroupOf d'.ker) := by
  refine Nat.card_congr (QuotientAddGroup.congr (N.range.addSubgroupOf d.ker) (N'.range.addSubgroupOf d'.ker)
    (kerEquiv Θ d d' hd) ?_).toEquiv
  ext ⟨b, hb⟩
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨x, hx⟩, hab⟩
    refine ⟨Θ x, ?_⟩
    have : Θ a = b := congrArg Subtype.val hab
    rw [← hN, hx]
    exact this
  · rintro ⟨y, hy⟩
    refine ⟨⟨Θ.symm b, ?_⟩, ⟨Θ.symm y, ?_⟩, Subtype.ext (Θ.apply_symm_apply b)⟩
    · rw [AddMonoidHom.mem_ker, ← Θ.injective.eq_iff, hd, AddEquiv.apply_symm_apply, map_zero]; exact hb
    · rw [← Θ.injective.eq_iff, hN, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hy]

theorem exists_conj (Θ : A ≃+ B) (d : A →+ A) : ∃ d' : B →+ B, ∀ a, Θ (d a) = d' (Θ a) :=
  ⟨Θ.toAddMonoidHom.comp (d.comp Θ.symm.toAddMonoidHom), fun a => by
    show Θ (d a) = Θ (d (Θ.symm (Θ a)))
    rw [AddEquiv.symm_apply_apply]⟩

end generic

theorem small (L : Type uL) [Field L] [NumberField L] : Small.{0} L :=
  haveI : Countable L := Countable.of_equiv _ (Module.finBasis ℚ L).equivFun.toEquiv.symm
  inferInstance

attribute [local instance] small

section models
variable (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def eqv : L ≃+* Shrink.{0} L := (Shrink.ringEquiv L).symm

theorem numberField : NumberField (Shrink.{0} L) := NumberField.of_ringEquiv L _ (eqv L)
attribute [local instance] numberField

@[reducible] def alg : Algebra (Shrink.{0} K) (Shrink.{0} L) :=
  ((eqv L : L →+* Shrink.{0} L).comp ((algebraMap K L).comp ((eqv K).symm : Shrink.{0} K →+* K))).toAlgebra
attribute [local instance] alg

theorem algebraMap_eqv (k : K) : algebraMap (Shrink.{0} K) (Shrink.{0} L) (eqv K k) = eqv L (algebraMap K L k) := by
  show eqv L (algebraMap K L ((eqv K).symm (eqv K k))) = _
  rw [RingEquiv.symm_apply_apply]

theorem algebraMap_comp_eqv : (algebraMap (Shrink.{0} K) (Shrink.{0} L)).comp (eqv K : K →+* Shrink.{0} K)
    = (eqv L : L →+* Shrink.{0} L).comp (algebraMap K L) :=
  RingHom.ext (algebraMap_eqv K L)

theorem isGalois [IsGalois K L] : IsGalois (Shrink.{0} K) (Shrink.{0} L) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  exact IsGalois.of_equiv_equiv (F := K) (E := L) (f := eqv K) (g := eqv L) (algebraMap_comp_eqv K L)

def gal (σ : L ≃ₐ[K] L) : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L :=
  AlgEquiv.ofRingEquiv (f := ((eqv L).symm.trans (σ : L ≃+* L)).trans (eqv L)) (fun x => by
    obtain ⟨k, rfl⟩ := (eqv K).surjective x
    show eqv L (σ ((eqv L).symm (algebraMap _ _ (eqv K k)))) = _
    rw [algebraMap_eqv, RingEquiv.symm_apply_apply, AlgEquiv.commutes])

theorem gal_apply (σ : L ≃ₐ[K] L) (x : L) : gal K L σ (eqv L x) = eqv L (σ x) := by
  show eqv L (σ ((eqv L).symm (eqv L x))) = _
  rw [RingEquiv.symm_apply_apply]

theorem eqv_symm_gal (σ : L ≃ₐ[K] L) (y : Shrink.{0} L) : (eqv L).symm (gal K L σ y) = σ ((eqv L).symm y) := by
  obtain ⟨x, rfl⟩ := (eqv L).surjective y
  rw [gal_apply, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

def galInv (τ : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) : L ≃ₐ[K] L :=
  AlgEquiv.ofRingEquiv (f := ((eqv L).trans (τ : Shrink.{0} L ≃+* Shrink.{0} L)).trans (eqv L).symm) (fun k => by
    show (eqv L).symm (τ (eqv L (algebraMap K L k))) = _
    rw [← algebraMap_eqv, AlgEquiv.commutes, algebraMap_eqv, RingEquiv.symm_apply_apply])

def galEquiv : (L ≃ₐ[K] L) ≃* (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) where
  toFun := gal K L
  invFun := galInv K L
  left_inv σ := AlgEquiv.ext fun x => by
    show (eqv L).symm (gal K L σ (eqv L x)) = σ x
    rw [gal_apply, RingEquiv.symm_apply_apply]
  right_inv τ := AlgEquiv.ext fun y => by
    obtain ⟨x, rfl⟩ := (eqv L).surjective y
    rw [gal_apply]
    show eqv L ((eqv L).symm (τ (eqv L x))) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' σ τ := AlgEquiv.ext fun y => by
    obtain ⟨x, rfl⟩ := (eqv L).surjective y
    rw [gal_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, gal_apply, gal_apply]

theorem galEquiv_apply (σ : L ≃ₐ[K] L) : galEquiv K L σ = gal K L σ := rfl

theorem card_gal : Nat.card (L ≃ₐ[K] L) = Nat.card (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) :=
  Nat.card_congr (galEquiv K L).toEquiv

theorem gal_generates {σ : L ≃ₐ[K] L} (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (τ : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) : τ ∈ Subgroup.zpowers (gal K L σ) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ ((galEquiv K L).symm τ))
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← galEquiv_apply, ← map_zpow, hk, MulEquiv.apply_symm_apply]⟩

theorem gal_inv (σ : L ≃ₐ[K] L) : gal K L σ⁻¹ = (gal K L σ)⁻¹ := by
  rw [← galEquiv_apply, map_inv]; rfl

theorem gal_pow (σ : L ≃ₐ[K] L) (i : ℕ) : gal K L (σ ^ i) = (gal K L σ) ^ i := by
  rw [← galEquiv_apply, map_pow]; rfl

def rint : 𝓞 L ≃+* 𝓞 (Shrink.{0} L) := RingOfIntegers.mapRingEquiv (eqv L)

theorem coe_rint (x : 𝓞 L) : ((rint L x : 𝓞 (Shrink.{0} L)) : Shrink.{0} L) = eqv L (x : L) := rfl

theorem coe_rint_symm (y : 𝓞 (Shrink.{0} L)) : (((rint L).symm y : 𝓞 L) : L) = (eqv L).symm (y : Shrink.{0} L) := rfl

theorem algebraMap_rint (x : 𝓞 K) :
    algebraMap (𝓞 (Shrink.{0} K)) (𝓞 (Shrink.{0} L)) (rint K x) = rint L (algebraMap (𝓞 K) (𝓞 L) x) :=
  Subtype.ext (algebraMap_eqv K L x)

theorem smul_rint (σ : L ≃ₐ[K] L) (x : 𝓞 L) : gal K L σ • rint L x = rint L (σ • x) :=
  Subtype.ext (gal_apply K L σ x)

def plc : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 (Shrink.{0} L)) :=
  HeightOneSpectrum.equivOfRingEquiv (rint L)

theorem mem_plc_iff (w : HeightOneSpectrum (𝓞 L)) (y : 𝓞 (Shrink.{0} L)) :
    y ∈ (plc L w).asIdeal ↔ (rint L).symm y ∈ w.asIdeal := Iff.rfl

theorem rint_mem_plc_iff (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) : rint L x ∈ (plc L w).asIdeal ↔ x ∈ w.asIdeal := by
  rw [mem_plc_iff, RingEquiv.symm_apply_apply]

theorem mem_plc_symm_iff (w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))) (x : 𝓞 L) :
    x ∈ ((plc L).symm w0).asIdeal ↔ rint L x ∈ w0.asIdeal := Iff.rfl

theorem under_plc (w : HeightOneSpectrum (𝓞 L)) :
    (plc L w).under (𝓞 (Shrink.{0} K)) = plc K (w.under (𝓞 K)) := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, rfl⟩ := (rint K).surjective y
  show (rint L).symm (algebraMap (𝓞 (Shrink.{0} K)) (𝓞 (Shrink.{0} L)) (rint K x)) ∈ w.asIdeal ↔
    (rint K).symm (rint K x) ∈ (w.under (𝓞 K)).asIdeal
  rw [algebraMap_rint, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  rfl

theorem plc_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : plc L (σ • w) = gal K L σ • plc L w := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, rfl⟩ := (rint L).surjective y
  rw [rint_mem_plc_iff, NumberField.PlaceTransport.mem_smul_asIdeal_iff, NumberField.PlaceTransport.mem_smul_asIdeal_iff,
    ← gal_inv, smul_rint, rint_mem_plc_iff]

theorem rint_mem_map_iff (J : Ideal (𝓞 L)) (z : 𝓞 L) : rint L z ∈ Ideal.map (rint L) J ↔ z ∈ J := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, e⟩ => (rint L).injective e ▸ hx, fun h => ⟨z, h, rfl⟩⟩

theorem plc_asIdeal (w : HeightOneSpectrum (𝓞 L)) : (plc L w).asIdeal = Ideal.map (rint L) w.asIdeal := by
  ext y
  obtain ⟨x, rfl⟩ := (rint L).surjective y
  rw [rint_mem_plc_iff, rint_mem_map_iff]

theorem rint_mem_plc_pow_iff (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) (z : 𝓞 L) :
    rint L z ∈ (plc L w).asIdeal ^ n ↔ z ∈ w.asIdeal ^ n := by
  rw [plc_asIdeal, ← Ideal.map_pow, rint_mem_map_iff]

theorem ramificationIdx_plc (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) :
    (plc K v).asIdeal.ramificationIdx' (plc L w).asIdeal = v.asIdeal.ramificationIdx' w.asIdeal := by
  unfold Ideal.ramificationIdx'
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, Ideal.map_le_iff_le_comap]
  constructor
  · intro h x hx
    have hx' := h ((rint_mem_plc_iff K v x).2 hx)
    rw [Ideal.mem_comap, algebraMap_rint, rint_mem_plc_pow_iff] at hx'
    rw [Ideal.mem_comap]
    exact hx'
  · intro h y hy
    obtain ⟨x, rfl⟩ := (rint K).surjective y
    rw [rint_mem_plc_iff] at hy
    rw [Ideal.mem_comap, algebraMap_rint, rint_mem_plc_pow_iff]
    exact h hy

variable {K L}

theorem hSram_model (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S → (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))) (hw0 : w0.under (𝓞 (Shrink.{0} K)) ∉ S.map (plc K).toEmbedding) :
    (w0.under (𝓞 (Shrink.{0} K))).asIdeal.ramificationIdx' w0.asIdeal = 1 := by
  obtain ⟨w, rfl⟩ := (plc L).surjective w0
  rw [under_plc] at hw0 ⊢
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hw0
  rw [ramificationIdx_plc]
  exact hSram w hw0

end models

attribute [local instance] numberField alg isGalois

section completion
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField.PlaceTransport

theorem intValuation_plc {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))}
    (hw : plc L w = w0) (r : 𝓞 L) : w0.intValuation (rint L r) = w.intValuation r := by
  subst hw
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have hr' : rint L r ≠ 0 := (RingEquiv.map_ne_zero_iff (rint L)).2 hr
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w.intValuation r = WithZero.exp (-(n : ℤ)) := ⟨_, w.intValuation_if_neg hr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, rint_mem_plc_pow_iff,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (plc L w).intValuation (rint L r) = WithZero.exp (-(n : ℤ)) :=
        ⟨_, (plc L w).intValuation_if_neg hr'⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, ← rint_mem_plc_pow_iff,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

theorem valuation_plc {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))}
    (hw : plc L w = w0) (x : L) : w0.valuation (Shrink.{0} L) (eqv L x) = w.valuation L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have h1 : ∀ c : 𝓞 L, eqv L (algebraMap (𝓞 L) L c) = algebraMap (𝓞 (Shrink.{0} L)) (Shrink.{0} L) (rint L c) :=
    fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_plc hw, intValuation_plc hw]

theorem valuation_plc_symm {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))}
    (hw : plc L w = w0) (y : Shrink.{0} L) : w.valuation L ((eqv L).symm y) = w0.valuation (Shrink.{0} L) y := by
  rw [← valuation_plc hw, RingEquiv.apply_symm_apply]

theorem uniformContinuous_congr_plc {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))}
    (hw : plc L w = w0) :
    UniformContinuous (WithVal.congr (w.valuation L) (w0.valuation (Shrink.{0} L)) (eqv L)) :=
  uniformContinuous_congr_of_forall_eq _ _ (w.valuation_surjective L) _ (valuation_plc hw)

theorem uniformContinuous_congr_plc_symm {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))}
    (hw : plc L w = w0) :
    UniformContinuous (WithVal.congr (w0.valuation (Shrink.{0} L)) (w.valuation L) (eqv L).symm) :=
  uniformContinuous_congr_of_forall_eq _ _ (w0.valuation_surjective _) _ (valuation_plc_symm hw)

def cpl {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))} (hw : plc L w = w0) :
    w.adicCompletion L ≃+* w0.adicCompletion (Shrink.{0} L) :=
  ((HeightOneSpectrum.adicCompletion.equiv L w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation L) (w0.valuation (Shrink.{0} L)) (eqv L))
      (uniformContinuous_congr_plc hw).continuous
      ((uniformContinuous_congr_plc_symm hw).continuous.congr fun _ => rfl))).trans
    (HeightOneSpectrum.adicCompletion.equiv (Shrink.{0} L) w0).symm

variable {w : HeightOneSpectrum (𝓞 L)} {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L))}

theorem cpl_apply (hw : plc L w = w0) (x : w.adicCompletion L) :
    (cpl hw x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation L) (w0.valuation (Shrink.{0} L)) (eqv L))
          x.toCompletion :=
  rfl

theorem cpl_coe (hw : plc L w = w0) (x : WithVal (w.valuation L)) :
    cpl hw (x : w.adicCompletion L)
      = ((WithVal.congr (w.valuation L) (w0.valuation (Shrink.{0} L)) (eqv L) x : WithVal (w0.valuation (Shrink.{0} L)))
          : w0.adicCompletion (Shrink.{0} L)) := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map (WithVal.congr (w.valuation L) (w0.valuation (Shrink.{0} L)) (eqv L))
      (x : (w.valuation L).Completion) = _
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_plc hw)]

theorem continuous_cpl (hw : plc L w = w0) : Continuous (cpl hw) := by
  rw [show (cpl hw : w.adicCompletion L → w0.adicCompletion (Shrink.{0} L)) =
      HeightOneSpectrum.adicCompletion.ofCompletion ∘ UniformSpace.Completion.map _ ∘
        HeightOneSpectrum.adicCompletion.toCompletion from
      funext fun x => HeightOneSpectrum.adicCompletion.ext _ _ (cpl_apply hw x)]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _).comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion _ _))

theorem valued_cpl (hw : plc L w = w0) (x : w.adicCompletion L) : Valued.v (cpl hw x) = Valued.v x := by
  have key : ∀ c : WithZero (Multiplicative ℤ), c ≠ 0 → ∀ y : w.adicCompletion L,
      (Valued.v (cpl hw y) ≤ c ↔ Valued.v y ≤ c) := by
    intro c hc y
    have hclosed : IsClosed {y : w.adicCompletion L | Valued.v (cpl hw y) ≤ c ↔ Valued.v y ≤ c} := by
      have h1 : IsClopen {y : w.adicCompletion L | Valued.v (cpl hw y) ≤ c} :=
        (isClopen_setOf_valued_le w0 hc).preimage (continuous_cpl hw)
      have h2 : IsClopen {y : w.adicCompletion L | Valued.v y ≤ c} := isClopen_setOf_valued_le w hc
      have : {y : w.adicCompletion L | Valued.v (cpl hw y) ≤ c ↔ Valued.v y ≤ c}
          = ({y | Valued.v (cpl hw y) ≤ c} ∩ {y | Valued.v y ≤ c}) ∪
            ({y | Valued.v (cpl hw y) ≤ c}ᶜ ∩ {y | Valued.v y ≤ c}ᶜ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact ((h1.inter h2).union (h1.compl.inter h2.compl)).isClosed
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective L w y
    refine UniformSpace.Completion.induction_on
      (p := fun y => Valued.v (cpl hw (HeightOneSpectrum.adicCompletion.ofCompletion y))
        ≤ c ↔ Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion L) ≤ c) y
      (hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _)) fun a => ?_
    show Valued.v (cpl hw (a : w.adicCompletion L)) ≤ c ↔ Valued.v (a : w.adicCompletion L) ≤ c
    rw [cpl_coe]
    show Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion _) ≤ c ↔
      Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion _) ≤ c
    rw [HeightOneSpectrum.adicCompletion.valued_ofCompletion, HeightOneSpectrum.adicCompletion.valued_ofCompletion,
      Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal,
      WithVal.congr_apply, WithVal.ofVal_toVal, valuation_plc hw]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h0' : Valued.v (cpl hw x) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero (cpl hw)).2 hx)
    exact le_antisymm ((key _ h0 x).2 le_rfl) ((key _ h0' x).1 le_rfl)

theorem cpl_mem_adicCompletionIntegers_iff (hw : plc L w = w0) (x : w.adicCompletion L) :
    cpl hw x ∈ w0.adicCompletionIntegers (Shrink.{0} L) ↔ x ∈ w.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, valued_cpl]

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in

def cplInt (hw : plc L w = w0) : w.adicCompletionIntegers L ≃+* w0.adicCompletionIntegers (Shrink.{0} L) where
  toFun x := ⟨cpl hw x, (cpl_mem_adicCompletionIntegers_iff hw _).2 x.2⟩
  invFun y := ⟨(cpl hw).symm y, (cpl_mem_adicCompletionIntegers_iff hw _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((cpl hw).symm_apply_apply x)
  right_inv y := Subtype.ext ((cpl hw).apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul (cpl hw) (x : w.adicCompletion L) (y : w.adicCompletion L))
  map_add' x y := Subtype.ext (map_add (cpl hw) (x : w.adicCompletion L) (y : w.adicCompletion L))

set_option synthInstance.maxHeartbeats 800000 in
theorem coe_cplInt (hw : plc L w = w0) (x : w.adicCompletionIntegers L) :
    ((cplInt hw x : w0.adicCompletionIntegers (Shrink.{0} L)) : w0.adicCompletion (Shrink.{0} L)) = cpl hw (x : w.adicCompletion L) :=
  rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem coe_cplInt_symm (hw : plc L w = w0) (y : w0.adicCompletionIntegers (Shrink.{0} L)) :
    (((cplInt hw).symm y : w.adicCompletionIntegers L) : w.adicCompletion L) = (cpl hw).symm (y : w0.adicCompletion (Shrink.{0} L)) :=
  rfl

theorem cpl_transport (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w')
    {w0 w0' : HeightOneSpectrum (𝓞 (Shrink.{0} L))} (hw : plc L w = w0) (hw' : plc L w' = w0')
    (h0 : gal K L σ • w0 = w0') (x : w.adicCompletion L) :
    cpl hw' (transport σ h x) = transport (gal K L σ) h0 (cpl hw x) := by
  obtain ⟨x, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective L w x
  refine UniformSpace.Completion.induction_on
    (p := fun x => cpl hw' (transport σ h (HeightOneSpectrum.adicCompletion.ofCompletion x))
      = transport (gal K L σ) h0 (cpl hw (HeightOneSpectrum.adicCompletion.ofCompletion x))) x
    (isClosed_eq ((continuous_cpl hw').comp ((continuous_transport σ h).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _)))
      ((continuous_transport (gal K L σ) h0).comp ((continuous_cpl hw).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _)))) fun a => ?_
  show cpl hw' (transport σ h (a : w.adicCompletion L)) = transport (gal K L σ) h0 (cpl hw (a : w.adicCompletion L))
  rw [transport_coe, cpl_coe, cpl_coe, transport_coe]
  congr 1
  simp only [WithVal.congr_apply, WithVal.ofVal_toVal, AlgEquiv.coe_ringEquiv, gal_apply]

end completion

section coord
variable (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
open NumberField.PlaceTransport

abbrev Fib (v : HeightOneSpectrum (𝓞 K)) : Type uL := {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}

abbrev Fib0 (v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))) : Type :=
  {w0 : HeightOneSpectrum (𝓞 (Shrink.{0} L)) // w0.under (𝓞 (Shrink.{0} K)) = v0}

theorem fib_cofinite (v : HeightOneSpectrum (𝓞 K)) : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, w.under (𝓞 K) ≠ v :=
  (M4aHerbrand.Bridge.tendsto_under_cofinite (𝓞 K) K L (𝓞 L)).eventually (Filter.eventually_cofinite_ne v)

theorem act_coord (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L)
    {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w') : (D.act σ x).2 w' = transport σ h (x.2 w) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  rw [Subsingleton.elim D (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x h

variable {K L}

theorem inv_smul_mem (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 K)} (w : Fib K L v) : (σ⁻¹ • w.1).under (𝓞 K) = v :=
  (NumberField.PlaceTransport.under_smul K L σ⁻¹ w.1).trans w.2

def sh (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 K)} (w : Fib K L v) : Fib K L v := ⟨σ⁻¹ • w.1, inv_smul_mem σ w⟩

theorem smul_sh (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 K)} (w : Fib K L v) : σ • (sh σ w).1 = w.1 := smul_inv_smul σ w.1

section ext
variable {v : HeightOneSpectrum (𝓞 K)}

open Classical in

def ext1 (u : Π w : Fib K L v, w.1.adicCompletion L) : FiniteAdeleRing (𝓞 L) L :=
  ⟨fun w => if h : w.under (𝓞 K) = v then u ⟨w, h⟩ else 1,
    (fib_cofinite K L v).mono fun w hw => by
      simp only [dif_neg hw]
      exact one_mem _⟩

open Classical in
theorem ext1_apply (u : Π w : Fib K L v, w.1.adicCompletion L) (w : Fib K L v) : ext1 u w.1 = u w := by
  obtain ⟨w, rfl⟩ := w
  show (if h : w.under (𝓞 K) = w.under (𝓞 K) then u ⟨w, h⟩ else 1) = u ⟨w, rfl⟩
  rw [dif_pos rfl]

end ext

section pinned
variable (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (S : Finset (HeightOneSpectrum (𝓞 K)))

private theorem _root_.P2mS26Univ.phiF_apply
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : Fib K L v.1, x w.1 = (u : Π w : Fib K L v.1, w.1.adicCompletion L) w) →
      ∀ w : Fib K L v.1, (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = (Φf v u : Π w : Fib K L v.1, w.1.adicCompletion L) w)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (w : Fib K L v.1) :
    (Φf v u : Π w : Fib K L v.1, w.1.adicCompletion L) w
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w)) := by
  rw [← hΦf v u (ext1 (u : Π w : Fib K L v.1, w.1.adicCompletion L)) (ext1_apply _) w,
    act_coord K L D σ _ (smul_sh σ w)]
  show transport σ (smul_sh σ w) (ext1 (u : Π w : Fib K L v.1, w.1.adicCompletion L) (sh σ w).1) = _
  rw [ext1_apply]

p2m_export "P2mS26Univ" "phiF_apply"
private theorem _root_.P2mS26Univ.phiB_apply
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : Fib K L v.1, x w.1 = ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : Fib K L v.1, (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = ((Φb v u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (w : Fib K L v.1) :
    ((Φb v u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)
      = transport σ (smul_sh σ w) ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) (sh σ w) : (sh σ w).1.adicCompletion L) := by
  rw [← hΦb v u (ext1 fun w => ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) (ext1_apply _) w,
    act_coord K L D σ _ (smul_sh σ w)]
  show transport σ (smul_sh σ w) (ext1 (fun w => ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) (sh σ w).1) = _
  rw [ext1_apply]

p2m_export "P2mS26Univ" "phiB_apply"
end pinned
end coord

section fibres
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev fplc {v : HeightOneSpectrum (𝓞 K)} {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))} (hv : plc K v = v0) (w : Fib K L v) :
    Fib0 K L v0 :=
  ⟨plc L w.1, by rw [under_plc, w.2, hv]⟩

abbrev fplcInv {v : HeightOneSpectrum (𝓞 K)} {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))} (hv : plc K v = v0) (w0 : Fib0 K L v0) :
    Fib K L v :=
  ⟨(plc L).symm w0.1, (plc K).injective (by rw [← under_plc, Equiv.apply_symm_apply, w0.2, hv])⟩

variable {v : HeightOneSpectrum (𝓞 K)} {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))}

theorem plc_fplcInv (hv : plc K v = v0) (w0 : Fib0 K L v0) : plc L (fplcInv (L := L) hv w0).1 = w0.1 :=
  Equiv.apply_symm_apply _ _

theorem fplc_fplcInv (hv : plc K v = v0) (w0 : Fib0 K L v0) : fplc hv (fplcInv (L := L) hv w0) = w0 :=
  Subtype.ext (plc_fplcInv hv w0)

theorem fplcInv_fplc (hv : plc K v = v0) (w : Fib K L v) : fplcInv hv (fplc (L := L) hv w) = w :=
  Subtype.ext (Equiv.symm_apply_apply _ _)

def fibEquiv (hv : plc K v = v0) : Fib K L v ≃ Fib0 K L v0 :=
  ⟨fplc hv, fplcInv hv, fplcInv_fplc hv, fplc_fplcInv hv⟩

theorem piF_aux1 (hv : plc K v = v0) (u : Π w : Fib K L v, w.1.adicCompletion L) (w w' : Fib K L v) (e : w' = w)
    (h' : plc L w'.1 = (fplc (L := L) hv w).1) :
    (cpl (rfl : plc L w.1 = (fplc (L := L) hv w).1)).symm (cpl h' (u w')) = u w := by
  subst e; exact RingEquiv.symm_apply_apply _ _

theorem piF_aux2 (u0 : Π w0 : Fib0 K L v0, w0.1.adicCompletion (Shrink.{0} L)) (w0 w0' : Fib0 K L v0) (e : w0' = w0)
    (w : HeightOneSpectrum (𝓞 L)) (h : plc L w = w0.1) (h' : plc L w = w0'.1) :
    cpl h ((cpl h').symm (u0 w0')) = u0 w0 := by
  subst e; exact RingEquiv.apply_symm_apply _ _

def piF (hv : plc K v = v0) :
    (Π w : Fib K L v, w.1.adicCompletion L) ≃+* (Π w0 : Fib0 K L v0, w0.1.adicCompletion (Shrink.{0} L)) where
  toFun u w0 := cpl (plc_fplcInv hv w0) (u (fplcInv hv w0))
  invFun u0 w := (cpl (rfl : plc L w.1 = (fplc (L := L) hv w).1)).symm (u0 (fplc hv w))
  left_inv u := funext fun w => piF_aux1 hv u w _ (fplcInv_fplc hv w) _
  right_inv u0 := funext fun w0 => piF_aux2 u0 w0 _ (fplc_fplcInv hv w0) _ _ _
  map_mul' u u' := funext fun w0 => by simp only [Pi.mul_apply, map_mul]
  map_add' u u' := funext fun w0 => by simp only [Pi.add_apply, map_add]

theorem piF_apply (hv : plc K v = v0) (u : Π w : Fib K L v, w.1.adicCompletion L) (w0 : Fib0 K L v0) :
    piF hv u w0 = cpl (plc_fplcInv hv w0) (u (fplcInv hv w0)) := rfl

theorem piF_symm_apply (hv : plc K v = v0) (u0 : Π w0 : Fib0 K L v0, w0.1.adicCompletion (Shrink.{0} L)) (w : Fib K L v) :
    (piF hv).symm u0 w = (cpl (rfl : plc L w.1 = (fplc (L := L) hv w).1)).symm (u0 (fplc hv w)) := rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem piB_aux1 (hv : plc K v = v0) (u : Π w : Fib K L v, w.1.adicCompletionIntegers L) (w w' : Fib K L v) (e : w' = w)
    (h' : plc L w'.1 = (fplc (L := L) hv w).1) :
    (cplInt (rfl : plc L w.1 = (fplc (L := L) hv w).1)).symm (cplInt h' (u w')) = u w := by
  subst e; exact RingEquiv.symm_apply_apply _ _

set_option synthInstance.maxHeartbeats 800000 in
theorem piB_aux2 (u0 : Π w0 : Fib0 K L v0, w0.1.adicCompletionIntegers (Shrink.{0} L)) (w0 w0' : Fib0 K L v0) (e : w0' = w0)
    (w : HeightOneSpectrum (𝓞 L)) (h : plc L w = w0.1) (h' : plc L w = w0'.1) :
    cplInt h ((cplInt h').symm (u0 w0')) = u0 w0 := by
  subst e; exact RingEquiv.apply_symm_apply _ _

set_option synthInstance.maxHeartbeats 800000 in

def piB (hv : plc K v = v0) :
    (Π w : Fib K L v, w.1.adicCompletionIntegers L) ≃+* (Π w0 : Fib0 K L v0, w0.1.adicCompletionIntegers (Shrink.{0} L)) where
  toFun u w0 := cplInt (plc_fplcInv hv w0) (u (fplcInv hv w0))
  invFun u0 w := (cplInt (rfl : plc L w.1 = (fplc (L := L) hv w).1)).symm (u0 (fplc hv w))
  left_inv u := funext fun w => piB_aux1 hv u w _ (fplcInv_fplc hv w) _
  right_inv u0 := funext fun w0 => piB_aux2 u0 w0 _ (fplc_fplcInv hv w0) _ _ _
  map_mul' u u' := funext fun w0 => by simp only [Pi.mul_apply, map_mul]
  map_add' u u' := funext fun w0 => by simp only [Pi.add_apply, map_add]

set_option synthInstance.maxHeartbeats 800000 in
theorem piB_apply (hv : plc K v = v0) (u : Π w : Fib K L v, w.1.adicCompletionIntegers L) (w0 : Fib0 K L v0) :
    piB hv u w0 = cplInt (plc_fplcInv hv w0) (u (fplcInv hv w0)) := rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem piB_symm_apply (hv : plc K v = v0) (u0 : Π w0 : Fib0 K L v0, w0.1.adicCompletionIntegers (Shrink.{0} L)) (w : Fib K L v) :
    (piB hv).symm u0 w = (cplInt (rfl : plc L w.1 = (fplc (L := L) hv w).1)).symm (u0 (fplc hv w)) := rfl

abbrev ΨF (hv : plc K v = v0) :
    (Π w : Fib K L v, w.1.adicCompletion L)ˣ ≃* (Π w0 : Fib0 K L v0, w0.1.adicCompletion (Shrink.{0} L))ˣ :=
  Units.mapEquiv (piF hv).toMulEquiv

set_option synthInstance.maxHeartbeats 800000 in
abbrev ΨB (hv : plc K v = v0) :
    (Π w : Fib K L v, w.1.adicCompletionIntegers L)ˣ ≃* (Π w0 : Fib0 K L v0, w0.1.adicCompletionIntegers (Shrink.{0} L))ˣ :=
  Units.mapEquiv (piB hv).toMulEquiv

end fibres

section products
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev S0 : Finset (HeightOneSpectrum (𝓞 (Shrink.{0} K))) := S.map (plc K).toEmbedding

variable {S}

abbrev splc (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S} :=
  ⟨plc K v.1, Finset.mem_map_equiv.2 (by rw [Equiv.symm_apply_apply]; exact v.2)⟩

abbrev splcInv (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) : {v : HeightOneSpectrum (𝓞 K) // v ∈ S} :=
  ⟨(plc K).symm v0.1, Finset.mem_map_equiv.1 v0.2⟩

abbrev snplc (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S} :=
  ⟨plc K v.1, fun h => v.2 (by rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at h; exact h)⟩

abbrev snplcInv (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S}) : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} :=
  ⟨(plc K).symm v0.1, fun h => v0.2 (Finset.mem_map_equiv.2 h)⟩

theorem hv0 (v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))) : plc K ((plc K).symm v0) = v0 := Equiv.apply_symm_apply _ _

theorem splc_splcInv (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) : splc (splcInv v0) = v0 :=
  Subtype.ext (hv0 v0.1)
theorem splcInv_splc (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) : splcInv (splc v) = v :=
  Subtype.ext (Equiv.symm_apply_apply _ _)
theorem snplc_snplcInv (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S}) : snplc (snplcInv v0) = v0 :=
  Subtype.ext (hv0 v0.1)
theorem snplcInv_snplc (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) : snplcInv (snplc v) = v :=
  Subtype.ext (Equiv.symm_apply_apply _ _)

abbrev XF : Type _ := Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}, (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ
abbrev XB : Type _ := Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ

abbrev XF0 : Type := Π v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S},
  (Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L))ˣ
abbrev XB0 : Type := Π v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S},
  (Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L)))ˣ

theorem ΨS_aux1 (U : XF L (S := S)) (v v' : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (e : v' = v) (h' : plc K v'.1 = (splc v).1) :
    (ΨF (L := L) (rfl : plc K v.1 = (splc v).1)).symm (ΨF h' (U v')) = U v := by
  subst e; exact MulEquiv.symm_apply_apply _ _
theorem ΨS_aux2 (U0 : XF0 L (S := S)) (v0 v0' : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) (e : v0' = v0)
    (v : HeightOneSpectrum (𝓞 K)) (h : plc K v = v0.1) (h' : plc K v = v0'.1) :
    ΨF (L := L) h ((ΨF h').symm (U0 v0')) = U0 v0 := by
  subst e; exact MulEquiv.apply_symm_apply _ _

def ΨS : XF L (S := S) ≃* XF0 L (S := S) where
  toFun U v0 := ΨF (hv0 v0.1) (U (splcInv v0))
  invFun U0 v := (ΨF (rfl : plc K v.1 = (splc v).1)).symm (U0 (splc v))
  left_inv U := funext fun v => ΨS_aux1 L U v _ (splcInv_splc v) _
  right_inv U0 := funext fun v0 => ΨS_aux2 L U0 v0 _ (splc_splcInv v0) _ _ _
  map_mul' U U' := funext fun v0 => map_mul (ΨF (L := L) (hv0 v0.1)) _ _

set_option synthInstance.maxHeartbeats 800000 in
theorem ΨT_aux1 (U : XB L (S := S)) (v v' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (e : v' = v) (h' : plc K v'.1 = (snplc v).1) :
    (ΨB (L := L) (rfl : plc K v.1 = (snplc v).1)).symm (ΨB h' (U v')) = U v := by
  subst e; exact MulEquiv.symm_apply_apply _ _
set_option synthInstance.maxHeartbeats 800000 in
theorem ΨT_aux2 (U0 : XB0 L (S := S)) (v0 v0' : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S}) (e : v0' = v0)
    (v : HeightOneSpectrum (𝓞 K)) (h : plc K v = v0.1) (h' : plc K v = v0'.1) :
    ΨB (L := L) h ((ΨB h').symm (U0 v0')) = U0 v0 := by
  subst e; exact MulEquiv.apply_symm_apply _ _

set_option synthInstance.maxHeartbeats 800000 in

def ΨT : XB L (S := S) ≃* XB0 L (S := S) where
  toFun U v0 := ΨB (hv0 v0.1) (U (snplcInv v0))
  invFun U0 v := (ΨB (rfl : plc K v.1 = (snplc v).1)).symm (U0 (snplc v))
  left_inv U := funext fun v => ΨT_aux1 L U v _ (snplcInv_snplc v) _
  right_inv U0 := funext fun v0 => ΨT_aux2 L U0 v0 _ (snplc_snplcInv v0) _ _ _
  map_mul' U U' := funext fun v0 => map_mul (ΨB (L := L) (hv0 v0.1)) _ _

def Ψ : XF L (S := S) × XB L (S := S) ≃* XF0 L (S := S) × XB0 L (S := S) := MulEquiv.prodCongr (ΨS L) (ΨT L)

def Θ : Additive (XF L (S := S) × XB L (S := S)) ≃+ Additive (XF0 L (S := S) × XB0 L (S := S)) := MulEquiv.toAdditive (Ψ L)

theorem Θ_ofMul (U : XF L (S := S) × XB L (S := S)) : Θ L (Additive.ofMul U) = Additive.ofMul (Ψ L U) := rfl
theorem Θ_symm_ofMul (U0 : XF0 L (S := S) × XB0 L (S := S)) : (Θ L).symm (Additive.ofMul U0) = Additive.ofMul ((Ψ L).symm U0) := rfl

def PhiF0 (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → MulAut (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) :
    MulAut (Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L))ˣ :=
  MulAut.congr (ΨF (hv0 v0.1)) (Φf (splcInv v0))

set_option synthInstance.maxHeartbeats 800000 in
def PhiB0 (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → MulAut (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S}) :
    MulAut (Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L)))ˣ :=
  MulAut.congr (ΨB (hv0 v0.1)) (Φb (snplcInv v0))

theorem PhiF0_pow (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → MulAut (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (i : ℕ) (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) :
    PhiF0 L (fun v => Φf v ^ i) v0 = PhiF0 L Φf v0 ^ i :=
  map_pow (MulAut.congr _) _ _

set_option synthInstance.maxHeartbeats 800000 in
theorem PhiB0_pow (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → MulAut (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (i : ℕ) (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S}) :
    PhiB0 L (fun v => Φb v ^ i) v0 = PhiB0 L Φb v0 ^ i :=
  map_pow (MulAut.congr _) _ _

theorem Ψ_symm_fst_aux (U0 : XF0 L (S := S)) (v0 v0' : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) (e : v0' = v0)
    (v : HeightOneSpectrum (𝓞 K)) (h : plc K v = v0.1) (h' : plc K v = v0'.1) :
    (ΨF (L := L) h').symm (U0 v0') = (ΨF h).symm (U0 v0) := by
  subst e; rfl

set_option synthInstance.maxHeartbeats 800000 in
theorem Ψ_symm_snd_aux (U0 : XB0 L (S := S)) (v0 v0' : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S}) (e : v0' = v0)
    (v : HeightOneSpectrum (𝓞 K)) (h : plc K v = v0.1) (h' : plc K v = v0'.1) :
    (ΨB (L := L) h').symm (U0 v0') = (ΨB h).symm (U0 v0) := by
  subst e; rfl

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in

theorem Ψ_componentwise
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → MulAut (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → MulAut (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (U0 : XF0 L (S := S) × XB0 L (S := S)) :
    Ψ L ((fun v => Φf v (((Ψ L).symm U0).1 v), fun v => Φb v (((Ψ L).symm U0).2 v)) : XF L (S := S) × XB L (S := S))
      = ((fun v0 => PhiF0 L Φf v0 (U0.1 v0), fun v0 => PhiB0 L Φb v0 (U0.2 v0)) : XF0 L (S := S) × XB0 L (S := S)) := by
  refine Prod.ext (funext fun v0 => ?_) (funext fun v0 => ?_)
  · show ΨF (hv0 v0.1) (Φf (splcInv v0) ((ΨF (rfl : plc K (splcInv v0).1 = (splc (splcInv v0)).1)).symm (U0.1 (splc (splcInv v0)))))
      = ΨF (hv0 v0.1) (Φf (splcInv v0) ((ΨF (hv0 v0.1)).symm (U0.1 v0)))
    rw [Ψ_symm_fst_aux L U0.1 v0 _ (splc_splcInv v0) _ (hv0 v0.1)]
  · show ΨB (hv0 v0.1) (Φb (snplcInv v0) ((ΨB (rfl : plc K (snplcInv v0).1 = (snplc (snplcInv v0)).1)).symm (U0.2 (snplc (snplcInv v0)))))
      = ΨB (hv0 v0.1) (Φb (snplcInv v0) ((ΨB (hv0 v0.1)).symm (U0.2 v0)))
    rw [Ψ_symm_snd_aux L U0.2 v0 _ (snplc_snplcInv v0) _ (hv0 v0.1)]

end products

section descent
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
open NumberField.PlaceTransport

theorem transport_fib0_aux (τ : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L) {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))}
    (u0 : Π w0 : Fib0 K L v0, w0.1.adicCompletion (Shrink.{0} L)) (w0 : Fib0 K L v0)
    (A B : Fib0 K L v0) (e : A = B) (hA : τ • A.1 = w0.1) (hB : τ • B.1 = w0.1) :
    transport τ hA (u0 A) = transport τ hB (u0 B) := by
  subst e; rfl

variable (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem fplc_sh {v : HeightOneSpectrum (𝓞 K)} {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))} (hv : plc K v = v0) (w0 : Fib0 K L v0) :
    (fplc hv (sh σ (fplcInv (L := L) hv w0))).1 = (gal K L σ)⁻¹ • w0.1 := by
  show plc L (σ⁻¹ • ((plc L).symm w0.1)) = _
  rw [plc_smul, gal_inv, Equiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in

theorem hPhiF0
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ ≃* (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) (u : (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ) (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : Fib K L v.1, x w.1 = (u : Π w : Fib K L v.1, w.1.adicCompletion L) w) →
      ∀ w : Fib K L v.1, (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = (Φf v u : Π w : Fib K L v.1, w.1.adicCompletion L) w)
    (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S})
    (u0 : (Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L))ˣ)
    (x0 : FiniteAdeleRing (𝓞 (Shrink.{0} L)) (Shrink.{0} L))
    (hx : ∀ w0 : Fib0 K L v0.1, x0 w0.1 = (u0 : Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L)) w0)
    (w0 : Fib0 K L v0.1) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum (Shrink.{0} K) (Shrink.{0} L)).act (gal K L σ)
        ((1 : InfiniteAdeleRing (Shrink.{0} L)), x0)).2 w0.1
      = (PhiF0 L Φf v0 u0 : Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L)) w0 := by

  have hsh0 : gal K L σ • ((gal K L σ)⁻¹ • w0.1) = w0.1 := smul_inv_smul _ _
  let sh0 : Fib0 K L v0.1 := ⟨(gal K L σ)⁻¹ • w0.1, (NumberField.PlaceTransport.under_smul _ _ _ w0.1).trans w0.2⟩
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply (Shrink.{0} K) (Shrink.{0} L) (gal K L σ) _ hsh0]
  have hx' : x0 ((gal K L σ)⁻¹ • w0.1) = (u0 : Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L)) sh0 := hx sh0

  have e : fplc (hv0 v0.1) (sh σ (fplcInv (hv0 v0.1) w0)) = sh0 := Subtype.ext (fplc_sh σ (hv0 v0.1) w0)
  have h0' : gal K L σ • plc L (sh σ (fplcInv (hv0 v0.1) w0)).1 = w0.1 := by
    have := congrArg Subtype.val e
    rw [show plc L (sh σ (fplcInv (hv0 v0.1) w0)).1 = (fplc (hv0 v0.1) (sh σ (fplcInv (hv0 v0.1) w0))).1 from rfl, this]
    exact hsh0
  show transport (gal K L σ) hsh0 (((1 : InfiniteAdeleRing (Shrink.{0} L)), x0).2 ((gal K L σ)⁻¹ • w0.1))
    = cpl (plc_fplcInv (hv0 v0.1) w0) ((Φf (splcInv v0) ((ΨF (hv0 v0.1)).symm u0) : Π w : Fib K L (splcInv v0).1, w.1.adicCompletion L) (fplcInv (hv0 v0.1) w0))
  rw [phiF_apply σ D S Φf hΦf (splcInv v0) _ (fplcInv (hv0 v0.1) w0)]
  show transport (gal K L σ) hsh0 (x0 ((gal K L σ)⁻¹ • w0.1))
    = cpl (plc_fplcInv (hv0 v0.1) w0) (transport σ (smul_sh σ (fplcInv (hv0 v0.1) w0))
        ((cpl (rfl : plc L (sh σ (fplcInv (hv0 v0.1) w0)).1 = plc L (sh σ (fplcInv (hv0 v0.1) w0)).1)).symm
          ((u0 : Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L)) (fplc (hv0 v0.1) (sh σ (fplcInv (hv0 v0.1) w0))))))
  rw [hx', cpl_transport σ (smul_sh σ (fplcInv (hv0 v0.1) w0)) rfl (plc_fplcInv (hv0 v0.1) w0) h0', RingEquiv.apply_symm_apply]
  exact transport_fib0_aux (gal K L σ) (u0 : Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L)) w0 _ _ e.symm hsh0 h0'

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in

theorem hPhiB0
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ ≃* (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (u : (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ) (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : Fib K L v.1, x w.1 = ((u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : Fib K L v.1, (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 = ((Φb v u : Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))
    (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∉ S0 S})
    (u0 : (Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L)))ˣ)
    (x0 : FiniteAdeleRing (𝓞 (Shrink.{0} L)) (Shrink.{0} L))
    (hx : ∀ w0 : Fib0 K L v0.1, x0 w0.1 = ((u0 : Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L))) w0 : w0.1.adicCompletion (Shrink.{0} L)))
    (w0 : Fib0 K L v0.1) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum (Shrink.{0} K) (Shrink.{0} L)).act (gal K L σ)
        ((1 : InfiniteAdeleRing (Shrink.{0} L)), x0)).2 w0.1
      = ((PhiB0 L Φb v0 u0 : Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L))) w0 : w0.1.adicCompletion (Shrink.{0} L)) := by
  have hsh0 : gal K L σ • ((gal K L σ)⁻¹ • w0.1) = w0.1 := smul_inv_smul _ _
  let sh0 : Fib0 K L v0.1 := ⟨(gal K L σ)⁻¹ • w0.1, (NumberField.PlaceTransport.under_smul _ _ _ w0.1).trans w0.2⟩
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply (Shrink.{0} K) (Shrink.{0} L) (gal K L σ) _ hsh0]
  have hx' : x0 ((gal K L σ)⁻¹ • w0.1) = ((u0 : Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L))) sh0 : sh0.1.adicCompletion (Shrink.{0} L)) := hx sh0
  have e : fplc (hv0 v0.1) (sh σ (fplcInv (hv0 v0.1) w0)) = sh0 := Subtype.ext (fplc_sh σ (hv0 v0.1) w0)
  have h0' : gal K L σ • plc L (sh σ (fplcInv (hv0 v0.1) w0)).1 = w0.1 := by
    have := congrArg Subtype.val e
    rw [show plc L (sh σ (fplcInv (hv0 v0.1) w0)).1 = (fplc (hv0 v0.1) (sh σ (fplcInv (hv0 v0.1) w0))).1 from rfl, this]
    exact hsh0
  show transport (gal K L σ) hsh0 (((1 : InfiniteAdeleRing (Shrink.{0} L)), x0).2 ((gal K L σ)⁻¹ • w0.1))
    = ((cplInt (plc_fplcInv (hv0 v0.1) w0) ((Φb (snplcInv v0) ((ΨB (hv0 v0.1)).symm u0) : Π w : Fib K L (snplcInv v0).1, ↥(w.1.adicCompletionIntegers L)) (fplcInv (hv0 v0.1) w0))
        : w0.1.adicCompletionIntegers (Shrink.{0} L)) : w0.1.adicCompletion (Shrink.{0} L))
  rw [coe_cplInt, phiB_apply σ D S Φb hΦb (snplcInv v0) _ (fplcInv (hv0 v0.1) w0)]
  show transport (gal K L σ) hsh0 (x0 ((gal K L σ)⁻¹ • w0.1))
    = cpl (plc_fplcInv (hv0 v0.1) w0) (transport σ (smul_sh σ (fplcInv (hv0 v0.1) w0))
        (((cplInt (rfl : plc L (sh σ (fplcInv (hv0 v0.1) w0)).1 = plc L (sh σ (fplcInv (hv0 v0.1) w0)).1)).symm
          ((u0 : Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L))) (fplc (hv0 v0.1) (sh σ (fplcInv (hv0 v0.1) w0)))) : (sh σ (fplcInv (hv0 v0.1) w0)).1.adicCompletionIntegers L) : (sh σ (fplcInv (hv0 v0.1) w0)).1.adicCompletion L))
  rw [hx', coe_cplInt_symm, cpl_transport σ (smul_sh σ (fplcInv (hv0 v0.1) w0)) rfl (plc_fplcInv (hv0 v0.1) w0) h0', RingEquiv.apply_symm_apply]
  exact transport_fib0_aux (gal K L σ) (fun w0 => ((u0 : Π w0 : Fib0 K L v0.1, ↥(w0.1.adicCompletionIntegers (Shrink.{0} L))) w0 : w0.1.adicCompletion (Shrink.{0} L))) w0 _ _ e.symm hsh0 h0'

end descent

section main
variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) {S : Finset (HeightOneSpectrum (𝓞 K))}
open NumberField.PlaceTransport

set_option maxHeartbeats 6400000 in

theorem hd0_of
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → MulAut (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → MulAut (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (d : Additive (XF L (S := S) × XB L (S := S)) →+ Additive (XF L (S := S) × XB L (S := S)))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (d0 : Additive (XF0 L (S := S) × XB0 L (S := S)) →+ Additive (XF0 L (S := S) × XB0 L (S := S)))
    (hd' : ∀ a, d0 (Θ L a) = Θ L (d a)) (u0 : XF0 L (S := S) × XB0 L (S := S)) :
    d0 (Additive.ofMul u0) =
      Additive.ofMul ((fun v0 => PhiF0 L Φf v0 (u0.1 v0), fun v0 => PhiB0 L Φb v0 (u0.2 v0))) - Additive.ofMul u0 := by
  have h := hd' ((Θ L).symm (Additive.ofMul u0))
  rw [AddEquiv.apply_symm_apply] at h
  have hdU := hd ((Ψ L).symm u0)
  rw [h, Θ_symm_ofMul, hdU, map_sub, Θ_ofMul, Θ_ofMul, MulEquiv.apply_symm_apply, Ψ_componentwise]

set_option maxHeartbeats 6400000 in

theorem hN0_of
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → MulAut (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → MulAut (Π w : Fib K L v.1, ↥(w.1.adicCompletionIntegers L))ˣ)
    (n : ℕ)
    (N : Additive (XF L (S := S) × XB L (S := S)) →+ Additive (XF L (S := S) × XB L (S := S)))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range n, Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))
    (N0 : Additive (XF0 L (S := S) × XB0 L (S := S)) →+ Additive (XF0 L (S := S) × XB0 L (S := S)))
    (hN' : ∀ a, N0 (Θ L a) = Θ L (N a)) (u0 : XF0 L (S := S) × XB0 L (S := S)) :
    N0 (Additive.ofMul u0) =
      ∑ i ∈ Finset.range n, Additive.ofMul ((fun v0 => (PhiF0 L Φf v0 ^ i) (u0.1 v0), fun v0 => (PhiB0 L Φb v0 ^ i) (u0.2 v0))) := by
  have h := hN' ((Θ L).symm (Additive.ofMul u0))
  rw [AddEquiv.apply_symm_apply] at h
  have hNU := hN ((Ψ L).symm u0)
  rw [h, Θ_symm_ofMul, hNU, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Θ_ofMul]
  have h1 := Ψ_componentwise L (fun v => Φf v ^ i) (fun v => Φb v ^ i) u0
  simp only [PhiF0_pow, PhiB0_pow] at h1
  exact congrArg Additive.ofMul h1

variable (K) in
theorem hsf0_of (sf : HeightOneSpectrum (𝓞 K) → ℕ) (hsf : ∀ v, sf v = Nat.card (Fib K L v))
    (v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K))) : sf ((plc K).symm v0) = Nat.card (Fib0 K L v0) :=
  (hsf _).trans (Nat.card_congr (fibEquiv (L := L) (hv0 v0)))

variable {L}

set_option maxHeartbeats 6400000 in

theorem descend (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = (u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          w.1.adicCompletion L) w) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          (Φf v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            w.1.adicCompletion L) w)
    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = ((u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          ((Φb v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))
    (d : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (N : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))
    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 := by
  obtain ⟨d0, hd'⟩ := exists_conj (Θ L (S := S)) d
  obtain ⟨N0, hN'⟩ := exists_conj (Θ L (S := S)) N
  have hd0 := hd0_of L Φf Φb d hd d0 (fun a => (hd' a).symm)
  have hN0 := hN0_of L Φf Φb (Nat.card (L ≃ₐ[K] L)) N hN N0 (fun a => (hN' a).symm)
  rw [card_gal K L] at hN0
  have key := P2mS26GL.finSIdeleFibreBox_u0 (Shrink.{0} K) (Shrink.{0} L)
    (gal K L σ) (gal_generates K L hσ) (S0 S) (hSram_model S hSram)
    (M4aHerbrand.GenuineDescent.genuineDescentDatum (Shrink.{0} K) (Shrink.{0} L))
    (PhiF0 L Φf) (fun v0 u0 x0 hx w0 => hPhiF0 σ D S Φf hΦf v0 u0 x0 hx w0)
    (PhiB0 L Φb) (fun v0 u0 x0 hx w0 => hPhiB0 σ D S Φb hΦb v0 u0 x0 hx w0)
    d0 hd0 N0 hN0
    (fun v0 => sf ((plc K).symm v0)) (hsf0_of K L sf hsf)
  refine ⟨?_, ?_⟩
  · rw [card_kerModRange_eq_of_addEquiv (Θ L) d N d0 N0 hd' hN', key.1, Finset.prod_map]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← card_gal, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  · rw [card_kerModRange_eq_of_addEquiv (Θ L) N d N0 d0 hN' hd', key.2]

end main

end

end P2mS26Univ

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (hSram : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1)

    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

    (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
    (hΦf : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = (u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          w.1.adicCompletion L) w) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          (Φf v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            w.1.adicCompletion L) w)

    (Φb : (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) →
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ ≃*
      (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
    (hΦb : ∀ (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
      (u : (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        ↥(w.1.adicCompletionIntegers L))ˣ)
      (x : FiniteAdeleRing (𝓞 L) L),
      (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        x w.1 = ((u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L)) →
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
        (D.act σ ((1 : InfiniteAdeleRing L), x)).2 w.1 =
          ((Φb v u : Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
            ↥(w.1.adicCompletionIntegers L)) w : w.1.adicCompletion L))

    (d : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hd : ∀ u, d (Additive.ofMul u) =
      Additive.ofMul ((fun v => Φf v (u.1 v), fun v => Φb v (u.2 v))) - Additive.ofMul u)
    (N : Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)) →+
      Additive ((Π v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1}, w.1.adicCompletion L)ˣ) ×
      (Π v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (Π w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v.1},
          ↥(w.1.adicCompletionIntegers L))ˣ)))
    (hN : ∀ u, N (Additive.ofMul u) =
      ∑ i ∈ Finset.range (Nat.card (L ≃ₐ[K] L)),
        Additive.ofMul ((fun v => (Φf v ^ i) (u.1 v), fun v => (Φb v ^ i) (u.2 v))))

    (sf : HeightOneSpectrum (𝓞 K) → ℕ)
    (hsf : ∀ v, sf v = Nat.card {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v}) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker)
        = ∏ v ∈ S, Nat.card (L ≃ₐ[K] L) / sf v
      ∧ Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = 1 :=
  P2mS26Univ.descend K L σ hσ S hSram D Φf hΦf Φb hΦb d hd N hN sf hsf

end S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd
end P2MW
export P2MW.S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd (solution)
