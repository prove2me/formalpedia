-- Prove2me | solution 1 for M4aHerbrand.nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/89113798-6237-51c0-9942-dd0f68d4d6ba

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_FiniteSIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localIntegerUnits
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

noncomputable section

namespace C6Aux

set_option linter.unusedSectionVars false

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

def OffT (T : Set (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 E)) : Prop := ∀ w ∈ T, w.under (𝓞 E) ≠ v

abbrev Idx (T : Set (HeightOneSpectrum (𝓞 F))) : Type := {v : HeightOneSpectrum (𝓞 E) // OffT (E := E) T v}

abbrev Fib (E : Type) [Field E] [NumberField E] [Algebra E F] (v : HeightOneSpectrum (𝓞 E)) : Type :=
  {w : HeightOneSpectrum (𝓞 F) // w.under (𝓞 E) = v}

abbrev P (E : Type) [Field E] [NumberField E] [Algebra E F] (T : Set (HeightOneSpectrum (𝓞 F))) : Type :=
  Π v : Idx (E := E) T, Π w : Fib (F := F) E v.1, (w.1.adicCompletionIntegers F)ˣ

variable (T : Set (HeightOneSpectrum (𝓞 F)))

theorem not_mem_of_offT {v : HeightOneSpectrum (𝓞 E)} (hv : OffT (E := E) T v) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w.under (𝓞 E) = v) : w ∉ T := fun hT => hv w hT hw

def toIntUnit (w : HeightOneSpectrum (𝓞 F)) (u : (w.adicCompletion F)ˣ)
    (h1 : (u : w.adicCompletion F) ∈ w.adicCompletionIntegers F)
    (h2 : ((u⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F) :
    (w.adicCompletionIntegers F)ˣ :=
  ⟨⟨u, h1⟩, ⟨(u⁻¹ : (w.adicCompletion F)ˣ), h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩

@[scoped simp] theorem coe_coe_toIntUnit (w : HeightOneSpectrum (𝓞 F)) (u : (w.adicCompletion F)ˣ) (h1 h2) :
    ((toIntUnit (F := F) w u h1 h2 : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F) = (u : w.adicCompletion F) := rfl

theorem finPart_mem (x : unitIdelesTrivialOn (𝓞 F) F T) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) :
    ((finPart w (x : (AdeleRing (𝓞 F) F)ˣ) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F :=
  (x.2.1 w hw).1

theorem finPart_inv_mem (x : unitIdelesTrivialOn (𝓞 F) F T) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) :
    (((finPart w (x : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
  rw [← map_inv]
  exact (x.2.1 w hw).2

def coords : unitIdelesTrivialOn (𝓞 F) F T →* P (F := F) E T where
  toFun x := fun v w => toIntUnit w.1 (finPart w.1 (x : (AdeleRing (𝓞 F) F)ˣ))
    (finPart_mem T x w.1 (not_mem_of_offT T v.2 w.2)) (finPart_inv_mem T x w.1 (not_mem_of_offT T v.2 w.2))
  map_one' := funext fun v => funext fun w => Units.ext (Subtype.ext (by simp))
  map_mul' x y := funext fun v => funext fun w => Units.ext (Subtype.ext (by simp))

theorem coe_coe_coords (x : unitIdelesTrivialOn (𝓞 F) F T) (v : Idx (E := E) T) (w : Fib (F := F) E v.1) :
    (((coords T x v w : (w.1.adicCompletionIntegers F)ˣ) : w.1.adicCompletionIntegers F) : w.1.adicCompletion F) =
      ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w.1 := rfl

open Classical in

def finAdeleOf (u : P (F := F) E T) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mk
    (fun w => if h : OffT (E := E) T (w.under (𝓞 E)) then
      (((u ⟨w.under (𝓞 E), h⟩ ⟨w, rfl⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F) : w.adicCompletion F)
      else 1)
    (Filter.Eventually.of_forall fun w => by
      change (if h : OffT (E := E) T (w.under (𝓞 E)) then _ else _) ∈ w.adicCompletionIntegers F
      split_ifs with h
      · exact SetLike.coe_mem _
      · exact one_mem _)

open Classical in
theorem finAdeleOf_apply (u : P (F := F) E T) (w : HeightOneSpectrum (𝓞 F)) :
    finAdeleOf T u w = if h : OffT (E := E) T (w.under (𝓞 E)) then
      (((u ⟨w.under (𝓞 E), h⟩ ⟨w, rfl⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F) : w.adicCompletion F)
      else 1 := rfl

theorem finAdeleOf_apply_of_offT (u : P (F := F) E T) (w : HeightOneSpectrum (𝓞 F)) (h : OffT (E := E) T (w.under (𝓞 E))) :
    finAdeleOf T u w =
      (((u ⟨w.under (𝓞 E), h⟩ ⟨w, rfl⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F) : w.adicCompletion F) := by
  rw [finAdeleOf_apply, dif_pos h]

theorem finAdeleOf_apply_of_not_offT (u : P (F := F) E T) (w : HeightOneSpectrum (𝓞 F)) (h : ¬ OffT (E := E) T (w.under (𝓞 E))) :
    finAdeleOf T u w = 1 := by
  rw [finAdeleOf_apply, dif_neg h]

theorem finAdeleOf_apply_mem (u : P (F := F) E T) (w : HeightOneSpectrum (𝓞 F)) :
    finAdeleOf T u w ∈ w.adicCompletionIntegers F := by
  by_cases h : OffT (E := E) T (w.under (𝓞 E))
  · rw [finAdeleOf_apply_of_offT T u w h]; exact SetLike.coe_mem _
  · rw [finAdeleOf_apply_of_not_offT T u w h]; exact one_mem _

theorem finAdeleOf_one : finAdeleOf T (1 : P (F := F) E T) = 1 := by
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases h : OffT (E := E) T (w.under (𝓞 E))
  · rw [finAdeleOf_apply_of_offT T _ w h]; rfl
  · rw [finAdeleOf_apply_of_not_offT T _ w h]; rfl

theorem finAdeleOf_mul (u u' : P (F := F) E T) : finAdeleOf T (u * u') = finAdeleOf T u * finAdeleOf T u' := by
  refine FiniteAdeleRing.ext _ fun w => ?_
  change finAdeleOf T (u * u') w = finAdeleOf T u w * finAdeleOf T u' w
  by_cases h : OffT (E := E) T (w.under (𝓞 E))
  · simp only [finAdeleOf_apply_of_offT T _ w h, Pi.mul_apply, Units.val_mul]
    rfl
  · simp only [finAdeleOf_apply_of_not_offT T _ w h, mul_one]

def adeleOfHom : P (F := F) E T →* AdeleRing (𝓞 F) F where
  toFun u := ((1 : InfiniteAdeleRing F), finAdeleOf T u)
  map_one' := Prod.ext rfl (finAdeleOf_one T)
  map_mul' u u' := Prod.ext (one_mul _).symm (finAdeleOf_mul T u u')

def ideleOf : P (F := F) E T →* (AdeleRing (𝓞 F) F)ˣ := (Units.map (adeleOfHom T)).comp toUnits.toMonoidHom

theorem coe_ideleOf (u : P (F := F) E T) : (ideleOf T u : AdeleRing (𝓞 F) F) = ((1 : InfiniteAdeleRing F), finAdeleOf T u) := rfl

theorem coe_ideleOf_inv (u : P (F := F) E T) :
    ((ideleOf T u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) = ideleOf T u⁻¹ := (map_inv (ideleOf T) u).symm

variable {T}

variable (T) in
theorem ideleOf_mem (u : P (F := F) E T) : ideleOf T u ∈ unitIdelesTrivialOn (𝓞 F) F T := by
  refine (mem_unitIdelesTrivialOn_iff T _).2 ⟨fun w _ => ⟨finAdeleOf_apply_mem T u w, ?_⟩, Units.ext rfl, fun w hw => ?_⟩
  · rw [coe_ideleOf_inv]; exact finAdeleOf_apply_mem T u⁻¹ w
  · refine Units.ext ?_
    rw [coe_finPart_apply, coe_ideleOf, Units.val_one]
    change finAdeleOf T u w = 1
    exact finAdeleOf_apply_of_not_offT T u w (fun h => h w hw rfl)

variable (T) in

def uOf : P (F := F) E T →* unitIdelesTrivialOn (𝓞 F) F T :=
  (ideleOf T).codRestrict _ (ideleOf_mem T)

variable (T) in
theorem coe_uOf (u : P (F := F) E T) : (uOf T u : (AdeleRing (𝓞 F) F)ˣ) = ideleOf T u := rfl

def μ (hTst : ∀ w w' : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) = w'.under (𝓞 E) → (w ∈ T ↔ w' ∈ T)) :
    unitIdelesTrivialOn (𝓞 F) F T ≃* P (F := F) E T :=
  { coords T with
    invFun := uOf T
    left_inv := fun x => by
      refine Subtype.ext (Units.ext (Prod.ext ?_ ?_))
      ·
        change (1 : InfiniteAdeleRing F) = ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
        exact (congrArg (fun z : (InfiniteAdeleRing F)ˣ => (z : InfiniteAdeleRing F)) x.2.2.1).symm
      · refine FiniteAdeleRing.ext _ fun w => ?_
        change finAdeleOf T (coords T x) w = ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
        by_cases h : OffT (E := E) T (w.under (𝓞 E))
        · rw [finAdeleOf_apply_of_offT T _ w h]; rfl
        · rw [finAdeleOf_apply_of_not_offT T _ w h]

          have hwT : w ∈ T := by
            by_contra hwT
            exact h fun w' hw' hww' => hwT ((hTst w' w hww').1 hw')
          exact (congrArg (fun z : (w.adicCompletion F)ˣ => (z : w.adicCompletion F)) (x.2.2.2 w hwT)).symm
    right_inv := fun u => by
      funext v w
      obtain ⟨v, hv⟩ := v
      obtain ⟨w, hw⟩ := w
      dsimp only at hw
      subst hw
      refine Units.ext (Subtype.ext ?_)
      change ((uOf T u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = _
      rw [coe_uOf, coe_ideleOf]
      change finAdeleOf T u w = _
      rw [finAdeleOf_apply_of_offT T u w hv] }

theorem coe_coe_μ (hTst : ∀ w w' : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) = w'.under (𝓞 E) → (w ∈ T ↔ w' ∈ T))
    (x : unitIdelesTrivialOn (𝓞 F) F T) (v : Idx (E := E) T) (w : Fib (F := F) E v.1) :
    (((μ hTst x v w : (w.1.adicCompletionIntegers F)ˣ) : w.1.adicCompletionIntegers F) : w.1.adicCompletion F) =
      ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w.1 := rfl

section equivariance

variable [IsGalois E F]
variable [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]

def pull (g : F ≃ₐ[E] F) {v : HeightOneSpectrum (𝓞 E)} (w : Fib (F := F) E v) : Fib (F := F) E v :=
  ⟨g⁻¹ • w.1, by rw [NumberField.PlaceTransport.under_smul]; exact w.2⟩

theorem smul_pull (g : F ≃ₐ[E] F) {v : HeightOneSpectrum (𝓞 E)} (w : Fib (F := F) E v) : g • (pull g w).1 = w.1 :=
  smul_inv_smul g w.1

theorem coe_smul_apply
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = (GenuineDescent.genuineDescentDatum E F).unitsAct g x)
    (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T) {v : HeightOneSpectrum (𝓞 E)} (w : Fib (F := F) E v) :
    (((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w.1 =
      NumberField.PlaceTransport.transport g (smul_pull g w) (((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 (pull g w).1) := by
  rw [hactU]
  exact GenuineDescent.genuineDescentDatum_act_snd_apply E F g _ (smul_pull g w)

end equivariance

end C6Aux
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits.C6Aux"

open C6Aux in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hTst : ∀ w w' : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) = w'.under (𝓞 E) → (w ∈ T ↔ w' ∈ T))
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x) :
    Nonempty (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T) ≅
      GroupCohomology.RepPi.obj (fun v : {v : HeightOneSpectrum (𝓞 E) // ∀ w ∈ T, w.under (𝓞 E) ≠ v} =>
        Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype (NumberField.FiniteSIdele.localIntegerUnits E F v.1))) := by
  classical

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _

  choose e he using fun v : Idx (E := E) (F := F) T =>
    NumberField.FiniteSIdele.exists_addEquiv_coind_localIntegerUnits E F v.1

  let Φ : Additive (unitIdelesTrivialOn (𝓞 F) F T) →
      (Π v : Idx (E := E) (F := F) T, Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype
        (NumberField.FiniteSIdele.localIntegerUnits E F v.1)) :=
    fun x v => (e v).symm (Additive.ofMul (μ hTst (Additive.toMul x) v))
  let Φ' : (Π v : Idx (E := E) (F := F) T, Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype
        (NumberField.FiniteSIdele.localIntegerUnits E F v.1)) → Additive (unitIdelesTrivialOn (𝓞 F) F T) :=
    fun f => Additive.ofMul ((μ hTst).symm (fun v => Additive.toMul (e v (f v))))
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => funext fun v => by
    simp only [Φ, toMul_add, map_mul, Pi.mul_apply, ofMul_mul, map_add, Pi.add_apply]
  let Ψ : Additive (unitIdelesTrivialOn (𝓞 F) F T) ≃ₗ[ℤ]
      (Π v : Idx (E := E) (F := F) T, Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype
        (NumberField.FiniteSIdele.localIntegerUnits E F v.1)) :=
    { toFun := Φ
      invFun := Φ'
      map_add' := hΦadd
      map_smul' := fun c x => by
        change Φ (SMul.smul c x) = SMul.smul c (Φ x)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact map_zsmul (AddMonoidHom.mk' Φ hΦadd) c x
      left_inv := fun x => by
        simp only [Φ, Φ', AddEquiv.apply_symm_apply, toMul_ofMul]
        rw [show (fun v => μ hTst (Additive.toMul x) v) = μ hTst (Additive.toMul x) from rfl, MulEquiv.symm_apply_apply,
          ofMul_toMul]
      right_inv := fun f => by
        funext v
        simp only [Φ, Φ', toMul_ofMul, MulEquiv.apply_symm_apply, ofMul_toMul, AddEquiv.symm_apply_apply] }
  refine ⟨Rep.mkIso (Representation.Equiv.mk Ψ fun g => LinearMap.ext fun x => funext fun v => ?_)⟩
  change Φ (Representation.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T) g x) v =
    (GroupCohomology.RepPi.piRepresentation _ g (Φ x)) v
  rw [GroupCohomology.RepPi.piRepresentation_apply, Representation.ofMulDistribMulAction_apply_apply]
  apply (e v).injective
  simp only [Φ, AddEquiv.apply_symm_apply, toMul_ofMul]
  apply Additive.toMul.injective
  funext w
  rw [toMul_ofMul, he v g _ w (pull g w) (smul_pull g w), AddEquiv.apply_symm_apply, toMul_ofMul]
  refine Units.ext (Subtype.ext ?_)
  change (((g • Additive.toMul x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w.1 =
    NumberField.PlaceTransport.transport g (smul_pull g w)
      ((((Additive.toMul x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 (pull g w).1)
  exact coe_smul_apply hactU g (Additive.toMul x) w

end
end S_M4aHerbrand_nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits
end P2MW
export P2MW.S_M4aHerbrand_nonempty_unitIdelesTrivialOn_iso_pi_coind_localIntegerUnits (solution)
