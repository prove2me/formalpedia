-- Prove2me | solution 1 for IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/25564a63-6fcc-5558-bbe2-0da61e9b20e8

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsLocalRing_finrank_invariants_linHom_units_modPow_eq
import Theorems.Thm_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq

set_option autoImplicit false
open Module
open scoped IntermediateField Pointwise

namespace PDevissage

section Basic
variable (A : Type*) [AddCommGroup A] (p : ℕ)

private def tor : AddSubgroup A := (DistribSMul.toAddMonoidHom A p).ker

private def pmul : AddSubgroup A := (DistribSMul.toAddMonoidHom A p).range

variable {A p}

private theorem mem_tor {a : A} : a ∈ tor A p ↔ p • a = 0 := Iff.rfl
private theorem mem_pmul {a : A} : a ∈ pmul A p ↔ ∃ a', p • a' = a := Iff.rfl

private scoped instance torModule [Fact p.Prime] : Module (ZMod p) (tor A p) :=
  AddCommGroup.zmodModule (fun x => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact mem_tor.mp x.2))

private scoped instance quotModule [Fact p.Prime] : Module (ZMod p) (A ⧸ pmul A p) :=
  AddCommGroup.zmodModule (by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact ⟨a, rfl⟩)

end Basic

section Functorial
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {p : ℕ} [Fact p.Prime]

private def torMap (f : A →+ B) : tor A p →ₗ[ZMod p] tor B p :=
  AddMonoidHom.toZModLinearMap p
    ((f.comp (tor A p).subtype).codRestrict (tor B p) (fun x => by
      rw [mem_tor, AddMonoidHom.comp_apply, ← map_nsmul, AddSubgroup.coe_subtype, ← AddSubgroup.coe_nsmul,
        show p • x = 0 from Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact mem_tor.mp x.2),
        AddSubgroup.coe_zero, map_zero]))

@[scoped simp] private theorem coe_torMap (f : A →+ B) (x : tor A p) : (torMap f x : B) = f x := rfl

private def quotMap (f : A →+ B) : (A ⧸ pmul A p) →ₗ[ZMod p] (B ⧸ pmul B p) :=
  AddMonoidHom.toZModLinearMap p
    (QuotientAddGroup.map (pmul A p) (pmul B p) f (by
      rintro _ ⟨a, rfl⟩; exact ⟨f a, by simp [map_nsmul]⟩))

@[scoped simp] private theorem quotMap_mk (f : A →+ B) (a : A) :
    quotMap (p := p) f (QuotientAddGroup.mk a) = QuotientAddGroup.mk (f a) := rfl

private theorem torMap_comp {C : Type*} [AddCommGroup C] (f : A →+ B) (g : B →+ C) :
    torMap (p := p) (g.comp f) = torMap g ∘ₗ torMap f := by
  ext x; rfl

private theorem quotMap_comp {C : Type*} [AddCommGroup C] (f : A →+ B) (g : B →+ C) :
    quotMap (p := p) (g.comp f) = quotMap g ∘ₗ quotMap f := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H a => rfl

private theorem torMap_id : torMap (p := p) (AddMonoidHom.id A) = LinearMap.id := by ext; rfl
private theorem quotMap_id : quotMap (p := p) (AddMonoidHom.id A) = LinearMap.id := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H a => rfl

end Functorial

section Action
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]

private def torRep (act : Δ →* AddAut A) : Representation (ZMod p) Δ (tor A p) where
  toFun d := torMap ((act d : A ≃+ A) : A →+ A)
  map_one' := by ext x; simp
  map_mul' d d' := by ext x; simp

private def quotRep (act : Δ →* AddAut A) : Representation (ZMod p) Δ (A ⧸ pmul A p) where
  toFun d := quotMap ((act d : A ≃+ A) : A →+ A)
  map_one' := by
    apply LinearMap.ext; intro x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp
  map_mul' d d' := by
    apply LinearMap.ext; intro x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp

@[scoped simp] private theorem coe_torRep (act : Δ →* AddAut A) (d : Δ) (x : tor A p) : (torRep act d x : A) = act d x := rfl
@[scoped simp] private theorem quotRep_mk (act : Δ →* AddAut A) (d : Δ) (a : A) :
    quotRep (p := p) act d (QuotientAddGroup.mk a) = QuotientAddGroup.mk (act d a) := rfl

end Action

end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage

section SubQuot
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)

private theorem act_inv_apply (d : Δ) (a : A) : act d⁻¹ (act d a) = a := by
  rw [← AddAut.mul_apply', ← map_mul, inv_mul_cancel, map_one, AddAut.one_apply']

private theorem act_apply_inv (d : Δ) (a : A) : act d (act d⁻¹ a) = a := by
  rw [← AddAut.mul_apply', ← map_mul, mul_inv_cancel, map_one, AddAut.one_apply']

include hB in
private theorem act_mem_iff (d : Δ) (a : A) : act d a ∈ B ↔ a ∈ B :=
  ⟨fun h => by simpa [act_inv_apply] using hB d⁻¹ _ h, hB d a⟩

private def subAct : Δ →* AddAut B where
  toFun d :=
    { toFun := fun b => ⟨act d b, hB d b b.2⟩
      invFun := fun b => ⟨act d⁻¹ b, hB d⁻¹ b b.2⟩
      left_inv := fun b => Subtype.ext (act_inv_apply act d b)
      right_inv := fun b => Subtype.ext (act_apply_inv act d b)
      map_add' := fun b b' => Subtype.ext (map_add _ _ _) }
  map_one' := by ext b; simp
  map_mul' d d' := by ext b; simp

@[scoped simp] private theorem coe_subAct (d : Δ) (b : B) : ((subAct act B hB d b : B) : A) = act d b := rfl

private def quotAct : Δ →* AddAut (A ⧸ B) where
  toFun d :=
    { toFun := QuotientAddGroup.map B B (act d : A ≃+ A) (fun a ha => hB d a ha)
      invFun := QuotientAddGroup.map B B (act d⁻¹ : A ≃+ A) (fun a ha => hB d⁻¹ a ha)
      left_inv := fun x => by
        induction x using QuotientAddGroup.induction_on with
        | H a => simp
      right_inv := fun x => by
        induction x using QuotientAddGroup.induction_on with
        | H a => simp
      map_add' := fun x y => map_add _ _ _ }
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp
  map_mul' d d' := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp

@[scoped simp] private theorem quotAct_mk (d : Δ) (a : A) :
    quotAct act B hB d (QuotientAddGroup.mk a) = QuotientAddGroup.mk (act d a) := rfl

end SubQuot
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage

section Snake
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)

local notation "C" => A ⧸ B

private def Ti : tor B p →ₗ[ZMod p] tor A p := torMap B.subtype

private def Tq : tor A p →ₗ[ZMod p] tor C p := torMap (QuotientAddGroup.mk' B)

private def Qi : (B ⧸ pmul B p) →ₗ[ZMod p] (A ⧸ pmul A p) := quotMap B.subtype

private def Qq : (A ⧸ pmul A p) →ₗ[ZMod p] (C ⧸ pmul C p) := quotMap (QuotientAddGroup.mk' B)

private theorem nsmul_out_mem (c : tor C p) : p • Quotient.out (c : C) ∈ B := by
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, QuotientAddGroup.out_eq']
  exact_mod_cast mem_tor.mp c.2

private theorem nsmul_mem_of_mk_eq (c : tor C p) (a : A) (ha : (QuotientAddGroup.mk a : C) = c) : p • a ∈ B := by
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ha]
  exact_mod_cast mem_tor.mp c.2

private noncomputable def delta₀ (c : tor C p) : B ⧸ pmul B p := QuotientAddGroup.mk ⟨p • Quotient.out (c : C), nsmul_out_mem B c⟩

private theorem delta₀_eq (c : tor C p) (a : A) (ha : (QuotientAddGroup.mk a : C) = c) :
    delta₀ B c = QuotientAddGroup.mk ⟨p • a, nsmul_mem_of_mk_eq B c a ha⟩ := by
  show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq]

  have hdiff : -Quotient.out (c : C) + a ∈ B := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', ha]
  refine ⟨⟨-Quotient.out (c : C) + a, hdiff⟩, Subtype.ext ?_⟩
  simp [smul_add]

private noncomputable def delta : tor C p →ₗ[ZMod p] (B ⧸ pmul B p) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := delta₀ B
      map_zero' := by
        rw [delta₀_eq B (0 : tor C p) 0 (by simp), QuotientAddGroup.eq_zero_iff]
        exact ⟨0, Subtype.ext (by simp)⟩
      map_add' := fun c c' => by
        rw [delta₀_eq B (c + c') (Quotient.out (c : C) + Quotient.out (c' : C)) (by simp)]
        show _ = (QuotientAddGroup.mk _ : B ⧸ pmul B p) + QuotientAddGroup.mk _
        rw [← QuotientAddGroup.mk_add]
        congr 1
        apply Subtype.ext
        simp [smul_add] }

private theorem delta_apply (c : tor C p) (a : A) (ha : (QuotientAddGroup.mk a : C) = c) :
    delta B c = QuotientAddGroup.mk ⟨p • a, nsmul_mem_of_mk_eq B c a ha⟩ :=
  delta₀_eq B c a ha

private theorem Ti_injective : Function.Injective (Ti (p := p) B) := by
  intro x y h
  have h' : ((x : B) : A) = ((y : B) : A) := congrArg (fun z : tor A p => (z : A)) h
  exact Subtype.ext (Subtype.ext h')

private theorem exact_Ti_Tq : Function.Exact (Ti (p := p) B) (Tq (p := p) B) := by
  intro x
  constructor
  · intro hx

    have hx' : ((x : A) : C) = 0 := congrArg (fun z : tor C p => (z : C)) hx
    rw [QuotientAddGroup.eq_zero_iff] at hx'
    have hpx : p • (x : A) = 0 := mem_tor.mp x.2
    refine ⟨⟨⟨x, hx'⟩, mem_tor.mpr (Subtype.ext ?_)⟩, Subtype.ext rfl⟩
    push_cast
    exact hpx
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    show ((((y : B) : A)) : C) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact (y : B).2

private theorem exact_Tq_delta : Function.Exact (Tq (p := p) B) (delta (p := p) B) := by
  intro c
  constructor
  · intro hc
    rw [delta_apply B c (Quotient.out (c : C)) (QuotientAddGroup.out_eq' _), QuotientAddGroup.eq_zero_iff] at hc
    obtain ⟨b, hb⟩ := hc

    have hb' : p • ((b : B) : A) = p • Quotient.out (c : C) := by
      have := congrArg (fun z : B => (z : A)) hb
      simpa using this
    refine ⟨⟨Quotient.out (c : C) - b, mem_tor.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [smul_sub, ← hb', sub_self]
    · show (QuotientAddGroup.mk (Quotient.out (c : C) - (b : A)) : C) = c
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq', (QuotientAddGroup.eq_zero_iff _).mpr b.2, sub_zero]
  · rintro ⟨a, rfl⟩
    rw [delta_apply B _ (a : A) rfl, QuotientAddGroup.eq_zero_iff]
    refine ⟨0, Subtype.ext ?_⟩
    show ((p • (0 : B) : B) : A) = p • (a : A)
    rw [smul_zero, ZeroMemClass.coe_zero]
    exact (mem_tor.mp a.2).symm

private theorem exact_delta_Qi : Function.Exact (delta (p := p) B) (Qi (p := p) B) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H b =>

      change (QuotientAddGroup.mk ((b : B) : A) : A ⧸ pmul A p) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      obtain ⟨a, ha⟩ := hx
      change p • a = _ at ha
      have hc : p • (QuotientAddGroup.mk a : C) = 0 := by
        rw [← QuotientAddGroup.mk_nsmul, ha, QuotientAddGroup.eq_zero_iff]; exact b.2
      refine ⟨⟨QuotientAddGroup.mk a, mem_tor.mpr hc⟩, ?_⟩
      rw [delta_apply B _ a rfl]
      congr 1
      exact Subtype.ext ha
  · rintro ⟨c, rfl⟩
    rw [delta_apply B c (Quotient.out (c : C)) (QuotientAddGroup.out_eq' _)]
    change (QuotientAddGroup.mk (p • Quotient.out (c : C)) : A ⧸ pmul A p) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨_, rfl⟩

private theorem exact_Qi_Qq : Function.Exact (Qi (p := p) B) (Qq (p := p) B) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      change (QuotientAddGroup.mk (QuotientAddGroup.mk a : C) : C ⧸ pmul C p) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      obtain ⟨c', hc'⟩ := hx
      change p • c' = _ at hc'
      induction c' using QuotientAddGroup.induction_on with
      | H a' =>

        have hmem : a - p • a' ∈ B := by
          rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul, hc', sub_self]
        refine ⟨QuotientAddGroup.mk ⟨a - p • a', hmem⟩, ?_⟩
        change (QuotientAddGroup.mk ((⟨a - p • a', hmem⟩ : B) : A) : A ⧸ pmul A p) = QuotientAddGroup.mk a
        rw [QuotientAddGroup.eq]
        exact ⟨a', by simp⟩
  · rintro ⟨y, rfl⟩
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      change (QuotientAddGroup.mk (QuotientAddGroup.mk ((b : B) : A) : C) : C ⧸ pmul C p) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).mpr b.2, QuotientAddGroup.mk_zero]

private theorem Qq_surjective : Function.Surjective (Qq (p := p) B) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    induction c using QuotientAddGroup.induction_on with
    | H a => exact ⟨QuotientAddGroup.mk a, rfl⟩

end Snake
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage

section HomExact
variable {k : Type*} [Field k] {Δ : Type*} [Group Δ]
variable {VN : Type*} [AddCommGroup VN] [Module k VN] (N : Representation k Δ VN)

private theorem mem_invariants_linHom_iff {VW : Type*} [AddCommGroup VW] [Module k VW] (W : Representation k Δ VW)
    (φ : VN →ₗ[k] VW) : φ ∈ (N.linHom W).invariants ↔ ∀ (d : Δ) (v : VN), φ (N d v) = W d (φ v) := by
  rw [Representation.mem_invariants]
  constructor
  · intro h d v
    have := LinearMap.congr_fun (h d) (N d v)
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply] at this
    rw [← this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro h d
    apply LinearMap.ext
    intro v
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable {VA VB VC : Type*} [AddCommGroup VA] [Module k VA] [AddCommGroup VB] [Module k VB]
  [AddCommGroup VC] [Module k VC]
  (PA : Representation k Δ VA) (PB : Representation k Δ VB) (PC : Representation k Δ VC)

private def postComp (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f) :
    (N.linHom PA).invariants →ₗ[k] (N.linHom PB).invariants where
  toFun φ := ⟨f ∘ₗ (φ : VN →ₗ[k] VA), by
    rw [mem_invariants_linHom_iff]
    intro d v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_invariants_linHom_iff N PA _).mp φ.2 d v]
    exact LinearMap.congr_fun (hf d) _⟩
  map_add' _ _ := Subtype.ext (by simp [LinearMap.comp_add])
  map_smul' _ _ := Subtype.ext (by simp [LinearMap.comp_smul])

@[scoped simp] private theorem coe_postComp (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f) (φ : (N.linHom PA).invariants) :
    ((postComp N PA PB f hf φ : (N.linHom PB).invariants) : VN →ₗ[k] VB) = f ∘ₗ (φ : VN →ₗ[k] VA) := rfl

private theorem postComp_injective (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f) (hinj : Function.Injective f) :
    Function.Injective (postComp N PA PB f hf) := by
  intro φ φ' h
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply hinj
  exact LinearMap.congr_fun (congrArg Subtype.val h) v

variable [Fintype Δ] [Invertible (Fintype.card Δ : k)]

private theorem exists_postComp_eq (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f)
    (φ : (N.linHom PB).invariants) (χ : VN →ₗ[k] VA) (hχ : f ∘ₗ χ = (φ : VN →ₗ[k] VB)) :
    ∃ ψ : (N.linHom PA).invariants, postComp N PA PB f hf ψ = φ := by
  classical
  refine ⟨⟨(N.linHom PA).averageMap χ, (N.linHom PA).averageMap_invariant χ⟩, Subtype.ext ?_⟩
  show f ∘ₗ (N.linHom PA).averageMap χ = (φ : VN →ₗ[k] VB)
  have hexp : (N.linHom PA).averageMap χ = ⅟(Fintype.card Δ : k) • ∑ d : Δ, (N.linHom PA) d χ := by
    simp [Representation.averageMap, GroupAlgebra.average, map_sum, LinearMap.sum_apply]
  have hterm : ∀ d : Δ, f ∘ₗ ((N.linHom PA) d χ) = (φ : VN →ₗ[k] VB) := by
    intro d
    apply LinearMap.ext
    intro v
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply]
    have hfx := LinearMap.congr_fun (hf d) (χ (N d⁻¹ v))
    simp only [LinearMap.coe_comp, Function.comp_apply] at hfx
    rw [hfx, show f (χ (N d⁻¹ v)) = (φ : VN →ₗ[k] VB) (N d⁻¹ v) from LinearMap.congr_fun hχ _,
      (mem_invariants_linHom_iff N PB _).mp φ.2 d⁻¹ v, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]
  rw [hexp, LinearMap.comp_smul]
  have hsum : f ∘ₗ (∑ d : Δ, (N.linHom PA) d χ) = ∑ d : Δ, f ∘ₗ ((N.linHom PA) d χ) := by
    apply LinearMap.ext; intro v; simp [LinearMap.sum_apply, map_sum]
  rw [hsum]
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

private theorem postComp_surjective (g : VB →ₗ[k] VC) (hg : ∀ d, g ∘ₗ PB d = PC d ∘ₗ g) (hsurj : Function.Surjective g) :
    Function.Surjective (postComp N PB PC g hg) := by
  intro φ
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  exact exists_postComp_eq N PB PC g hg φ (s ∘ₗ (φ : VN →ₗ[k] VC))
    (by rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp])

private theorem exact_postComp (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f)
    (g : VB →ₗ[k] VC) (hg : ∀ d, g ∘ₗ PB d = PC d ∘ₗ g) (hexact : Function.Exact f g) :
    Function.Exact (postComp N PA PB f hf) (postComp N PB PC g hg) := by
  intro φ
  constructor
  · intro hφ

    have hφ0 : ∀ v, g ((φ : VN →ₗ[k] VB) v) = 0 := fun v =>
      LinearMap.congr_fun (congrArg Subtype.val hφ) v
    have hrange : LinearMap.range (φ : VN →ₗ[k] VB) ≤ LinearMap.range f := by
      rintro _ ⟨v, rfl⟩
      exact (hexact _).mp (hφ0 v)
    obtain ⟨χ, hχ⟩ := Module.projective_lifting_property f.rangeRestrict
      ((φ : VN →ₗ[k] VB).codRestrict (LinearMap.range f) (fun v => hrange ⟨v, rfl⟩))
      (LinearMap.surjective_rangeRestrict f)
    have hχ' : f ∘ₗ χ = (φ : VN →ₗ[k] VB) := by
      apply LinearMap.ext; intro v
      exact congrArg Subtype.val (LinearMap.congr_fun hχ v)
    obtain ⟨ψ, hψ⟩ := exists_postComp_eq N PA PB f hf φ χ hχ'
    exact ⟨ψ, hψ⟩
  · rintro ⟨ψ, rfl⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact hexact.apply_apply_eq_zero _
end HomExact
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage
section Alt
variable {k : Type*} [Field k]
  {V₁ V₂ V₃ V₄ V₅ V₆ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
  [AddCommGroup V₆] [Module k V₆]
  [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃] [FiniteDimensional k V₄]
  [FiniteDimensional k V₅] [FiniteDimensional k V₆]

private theorem finrank_alternating_six (u₁ : V₁ →ₗ[k] V₂) (u₂ : V₂ →ₗ[k] V₃) (u₃ : V₃ →ₗ[k] V₄) (u₄ : V₄ →ₗ[k] V₅)
    (u₅ : V₅ →ₗ[k] V₆) (h₁ : Function.Injective u₁) (h₁₂ : Function.Exact u₁ u₂) (h₂₃ : Function.Exact u₂ u₃)
    (h₃₄ : Function.Exact u₃ u₄) (h₄₅ : Function.Exact u₄ u₅) (h₅ : Function.Surjective u₅) :
    finrank k V₁ + finrank k V₃ + finrank k V₅ = finrank k V₂ + finrank k V₄ + finrank k V₆ := by
  have r₁ := LinearMap.finrank_range_add_finrank_ker u₁
  have r₂ := LinearMap.finrank_range_add_finrank_ker u₂
  have r₃ := LinearMap.finrank_range_add_finrank_ker u₃
  have r₄ := LinearMap.finrank_range_add_finrank_ker u₄
  have r₅ := LinearMap.finrank_range_add_finrank_ker u₅
  have e₁ : finrank k (LinearMap.ker u₁) = 0 := by rw [LinearMap.ker_eq_bot.mpr h₁, finrank_bot]
  have e₂ : finrank k (LinearMap.ker u₂) = finrank k (LinearMap.range u₁) := by rw [h₁₂.linearMap_ker_eq]
  have e₃ : finrank k (LinearMap.ker u₃) = finrank k (LinearMap.range u₂) := by rw [h₂₃.linearMap_ker_eq]
  have e₄ : finrank k (LinearMap.ker u₄) = finrank k (LinearMap.range u₃) := by rw [h₃₄.linearMap_ker_eq]
  have e₅ : finrank k (LinearMap.ker u₅) = finrank k (LinearMap.range u₄) := by rw [h₄₅.linearMap_ker_eq]
  have e₆ : finrank k (LinearMap.range u₅) = finrank k V₆ := by rw [LinearMap.range_eq_top.mpr h₅, finrank_top]
  omega

end Alt
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage

section Equivariance
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)

local notation "C" => A ⧸ B

private theorem Ti_equivariant (d : Δ) :
    Ti (p := p) B ∘ₗ torRep (subAct act B hB) d = torRep act d ∘ₗ Ti (p := p) B := by
  ext x; rfl

private theorem Tq_equivariant (d : Δ) :
    Tq (p := p) B ∘ₗ torRep act d = torRep (quotAct act B hB) d ∘ₗ Tq (p := p) B := by
  ext x; rfl

private theorem Qi_equivariant (d : Δ) :
    Qi (p := p) B ∘ₗ quotRep (subAct act B hB) d = quotRep act d ∘ₗ Qi (p := p) B := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H b => rfl

private theorem Qq_equivariant (d : Δ) :
    Qq (p := p) B ∘ₗ quotRep act d = quotRep (quotAct act B hB) d ∘ₗ Qq (p := p) B := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H a => rfl

private theorem delta_equivariant (d : Δ) :
    delta (p := p) B ∘ₗ torRep (quotAct act B hB) d = quotRep (subAct act B hB) d ∘ₗ delta (p := p) B := by
  apply LinearMap.ext; intro c
  obtain ⟨a, ha⟩ : ∃ a : A, (QuotientAddGroup.mk a : C) = c := ⟨_, QuotientAddGroup.out_eq' _⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, delta_apply B c a ha,
    delta_apply B (torRep (quotAct act B hB) d c) (act d a) (by rw [← quotAct_mk act B hB, ha]; rfl)]
  show _ = QuotientAddGroup.mk _
  congr 1
  apply Subtype.ext
  show p • act d a = act d (p • a)
  rw [map_nsmul]

end Equivariance
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

section Engine
variable {Δ : Type*} [Group Δ] [Fintype Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
  (N : Representation (ZMod p) Δ VN)

local notation "C" => A ⧸ B

private theorem engine [Invertible (Fintype.card Δ : ZMod p)]
    [FiniteDimensional (ZMod p) (tor B p)] [FiniteDimensional (ZMod p) (tor A p)]
    [FiniteDimensional (ZMod p) (tor C p)] [FiniteDimensional (ZMod p) (B ⧸ pmul B p)]
    [FiniteDimensional (ZMod p) (A ⧸ pmul A p)] [FiniteDimensional (ZMod p) (C ⧸ pmul C p)] :
    finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) (subAct act B hB))).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) (quotAct act B hB))).invariants
    = finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants
      + finrank (ZMod p) (N.linHom (quotRep (p := p) (subAct act B hB))).invariants
      + finrank (ZMod p) (N.linHom (quotRep (p := p) (quotAct act B hB))).invariants := by
  have h := finrank_alternating_six
    (postComp N (torRep (subAct act B hB)) (torRep act) (Ti B) (Ti_equivariant act B hB))
    (postComp N (torRep act) (torRep (quotAct act B hB)) (Tq B) (Tq_equivariant act B hB))
    (postComp N (torRep (quotAct act B hB)) (quotRep (subAct act B hB)) (delta B) (delta_equivariant act B hB))
    (postComp N (quotRep (subAct act B hB)) (quotRep act) (Qi B) (Qi_equivariant act B hB))
    (postComp N (quotRep act) (quotRep (quotAct act B hB)) (Qq B) (Qq_equivariant act B hB))
    (postComp_injective N _ _ _ _ (Ti_injective B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_Ti_Tq B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_Tq_delta B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_delta_Qi B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_Qi_Qq B))
    (postComp_surjective N _ _ _ _ (Qq_surjective B))
  omega

end Engine
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage

section Aux
variable {k : Type*} [Field k] {Δ : Type*} [Group Δ]
variable {VN : Type*} [AddCommGroup VN] [Module k VN] (N : Representation k Δ VN)

private theorem finrank_hom_eq_of_equiv {VA VB : Type*} [AddCommGroup VA] [Module k VA] [AddCommGroup VB] [Module k VB]
    (PA : Representation k Δ VA) (PB : Representation k Δ VB) (e : VA ≃ₗ[k] VB)
    (he : ∀ (d : Δ) (a : VA), e (PA d a) = PB d (e a)) :
    finrank k (N.linHom PA).invariants = finrank k (N.linHom PB).invariants := by
  have hmemA := mem_invariants_linHom_iff N PA
  have hmemB := mem_invariants_linHom_iff N PB
  let E : (N.linHom PA).invariants ≃ₗ[k] (N.linHom PB).invariants :=
    { toFun := fun φ => ⟨e.toLinearMap ∘ₗ (φ : VN →ₗ[k] VA), (hmemB _).mpr fun d v => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [(hmemA _).mp φ.2 d v, he]⟩
      map_add' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_add])
      map_smul' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_smul])
      invFun := fun ψ => ⟨e.symm.toLinearMap ∘ₗ (ψ : VN →ₗ[k] VB), (hmemA _).mpr fun d v => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        apply e.injective
        rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
        exact (hmemB _).mp ψ.2 d v⟩
      left_inv := fun φ => Subtype.ext (LinearMap.ext fun v => by simp)
      right_inv := fun ψ => Subtype.ext (LinearMap.ext fun v => by simp) }
  exact LinearEquiv.finrank_eq E

private theorem finrank_hom_eq_zero_of_subsingleton {VA : Type*} [AddCommGroup VA] [Module k VA] [Subsingleton VA]
    (PA : Representation k Δ VA) : finrank k (N.linHom PA).invariants = 0 := by
  haveI : Subsingleton (VN →ₗ[k] VA) := inferInstance
  apply finrank_zero_of_subsingleton

end Aux
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

section Finite
variable {Δ : Type*} [Group Δ] [Fintype Δ] {p : ℕ} [Fact p.Prime]
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
  (N : Representation (ZMod p) Δ VN)

private theorem pmul_stable {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A) (d : Δ) (a : A) (ha : a ∈ pmul A p) :
    act d a ∈ pmul A p := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨act d a', (map_nsmul _ _ _).symm⟩

private theorem finrank_hom_tor_eq_quot_of_forall_nsmul_eq_zero {A : Type*} [AddCommGroup A] [Finite A]
    (act : Δ →* AddAut A) (hA : ∀ a : A, p • a = 0) :
    finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants
      = finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants := by

  have htor : ∀ a : A, a ∈ tor A p := fun a => mem_tor.mpr (hA a)
  have hpmul : pmul A p = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    exact hA a

  let f₀ : tor A p →+ A ⧸ pmul A p := (QuotientAddGroup.mk' (pmul A p)).comp (tor A p).subtype
  have hf₀_inj : Function.Injective f₀ := by
    intro x y h
    apply Subtype.ext
    have : ((x : A) : A ⧸ pmul A p) = (y : A) := h
    rwa [QuotientAddGroup.eq, hpmul, AddSubgroup.mem_bot, neg_add_eq_zero] at this
  have hf₀_surj : Function.Surjective f₀ := by
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H a => exact ⟨⟨a, htor a⟩, rfl⟩
  let e : tor A p ≃ₗ[ZMod p] (A ⧸ pmul A p) :=
    LinearEquiv.ofBijective (f₀.toZModLinearMap p) ⟨hf₀_inj, hf₀_surj⟩
  exact finrank_hom_eq_of_equiv N _ _ e (fun d a => rfl)

private scoped instance finiteDimensional_tor {A : Type*} [AddCommGroup A] [Finite A] :
    FiniteDimensional (ZMod p) (tor A p) :=
  Module.Finite.of_finite
private scoped instance finiteDimensional_quot {A : Type*} [AddCommGroup A] [Finite A] :
    FiniteDimensional (ZMod p) (A ⧸ pmul A p) :=
  Module.Finite.of_finite

private theorem finrank_hom_tor_eq_quot_of_finite [Invertible (Fintype.card Δ : ZMod p)] :
    ∀ (n : ℕ) (A : Type*) [AddCommGroup A] [Finite A] (act : Δ →* AddAut A), Nat.card A = n →
      finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants
        = finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ act hn
    by_cases htop : pmul A p = ⊤
    ·
      have hsurj : Function.Surjective (fun a : A => p • a) := fun a => by
        have : a ∈ pmul A p := htop ▸ AddSubgroup.mem_top a
        exact this
      have hinj : Function.Injective (fun a : A => p • a) := Finite.injective_iff_surjective.mpr hsurj
      haveI : Subsingleton (tor A p) := ⟨fun x y => Subtype.ext (hinj (by
        simp only [mem_tor.mp x.2, mem_tor.mp y.2]))⟩
      haveI : Subsingleton (A ⧸ pmul A p) := by
        rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
      rw [finrank_hom_eq_zero_of_subsingleton, finrank_hom_eq_zero_of_subsingleton]
    ·
      set B := pmul A p with hBdef
      have hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B := pmul_stable act
      haveI : Finite B := inferInstance
      haveI : Finite (A ⧸ B) := inferInstance
      have hcard : Nat.card B < n := by
        rw [← hn]
        have h1 : Nat.card B * B.index = Nat.card A := AddSubgroup.card_mul_index B
        have h2 : B.index ≠ 1 := fun h => htop (AddSubgroup.index_eq_one.mp h)
        have h3 : B.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
        have h4 : 0 < Nat.card A := Nat.card_pos
        have h5 : 2 ≤ B.index := by omega
        have h6 : Nat.card B * 2 ≤ Nat.card A := h1 ▸ Nat.mul_le_mul_left _ h5
        omega

      have hE := engine act B hB N
      have hIH := ih (Nat.card B) hcard B (subAct act B hB) rfl
      have hC : finrank (ZMod p) (N.linHom (torRep (p := p) (quotAct act B hB))).invariants
          = finrank (ZMod p) (N.linHom (quotRep (p := p) (quotAct act B hB))).invariants :=
        finrank_hom_tor_eq_quot_of_forall_nsmul_eq_zero N (quotAct act B hB) (fun c => by
          induction c using QuotientAddGroup.induction_on with
          | H a => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact ⟨a, rfl⟩)
      omega

end Finite
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage

section MainCanonical
variable {Δ : Type*} [Group Δ] [Fintype Δ] {p : ℕ} [Fact p.Prime]
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
  (N : Representation (ZMod p) Δ VN)

private theorem finrank_hom_canonical_eq [Invertible (Fintype.card Δ : ZMod p)]
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    [FiniteDimensional (ZMod p) (tor B p)] [FiniteDimensional (ZMod p) (tor A p)]
    [FiniteDimensional (ZMod p) (B ⧸ pmul B p)] [FiniteDimensional (ZMod p) (A ⧸ pmul A p)] :
    finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) (subAct act B hB))).invariants
    = finrank (ZMod p) (N.linHom (quotRep (p := p) (subAct act B hB))).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants := by
  haveI : Finite (A ⧸ B) := AddSubgroup.finite_quotient_of_finiteIndex
  have hE := engine act B hB N
  have hC := finrank_hom_tor_eq_quot_of_finite N (Nat.card (A ⧸ B)) (A ⧸ B) (quotAct act B hB) rfl
  omega

end MainCanonical
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

section Transfer
variable {Δ : Type*} [Group Δ] {p : ℕ} [Fact p.Prime]
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] (N : Representation (ZMod p) Δ VN)
variable {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)

private theorem quotPres_bijective {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) :
    Function.Bijective (QuotientAddGroup.lift (pmul A p) πA
      (by rintro _ ⟨a, rfl⟩; exact (hkerA _).mpr ⟨a, rfl⟩) : A ⧸ pmul A p →+ VA) := by
  constructor
  · intro x y h
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      induction y using QuotientAddGroup.induction_on with
      | H b =>
        change πA a = πA b at h
        rw [QuotientAddGroup.eq]
        have : πA (-a + b) = 0 := by rw [map_add, map_neg, h, neg_add_cancel]
        obtain ⟨a', ha'⟩ := (hkerA _).mp this
        exact ⟨a', ha'⟩
  · intro v
    obtain ⟨a, rfl⟩ := hπA v
    exact ⟨QuotientAddGroup.mk a, rfl⟩

private noncomputable def quotPresEquiv {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) :
    (A ⧸ pmul A p) ≃ₗ[ZMod p] VA :=
  LinearEquiv.ofBijective ((QuotientAddGroup.lift (pmul A p) πA
      (by rintro _ ⟨a, rfl⟩; exact (hkerA _).mpr ⟨a, rfl⟩)).toZModLinearMap p) (quotPres_bijective πA hπA hkerA)

private theorem quotPresEquiv_mk {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) (a : A) :
    quotPresEquiv πA hπA hkerA (QuotientAddGroup.mk a) = πA a := rfl

private theorem finrank_hom_quotPres_eq
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a)) :
    finrank (ZMod p) (N.linHom PA).invariants = finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants := by
  symm
  refine finrank_hom_eq_of_equiv N _ _ (quotPresEquiv πA hπA hkerA) (fun d x => ?_)
  induction x using QuotientAddGroup.induction_on with
  | H a => exact hπAΔ d a

private theorem finiteDimensional_quot_of_pres
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) :
    FiniteDimensional (ZMod p) (A ⧸ pmul A p) :=
  LinearEquiv.finiteDimensional (quotPresEquiv πA hπA hkerA).symm

private theorem torPres_bijective {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA]
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0) :
    Function.Bijective (ιA.codRestrict (tor A p) (fun w => mem_tor.mpr ((hranA _).mp ⟨w, rfl⟩))) := by
  constructor
  · exact fun x y h => hιA (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    obtain ⟨w, rfl⟩ := (hranA a).mpr (mem_tor.mp ha)
    exact ⟨w, rfl⟩

private noncomputable def torPresEquiv {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA]
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0) :
    WA ≃ₗ[ZMod p] tor A p :=
  LinearEquiv.ofBijective ((ιA.codRestrict (tor A p)
    (fun w => mem_tor.mpr ((hranA _).mp ⟨w, rfl⟩))).toZModLinearMap p) (torPres_bijective ιA hιA hranA)

private theorem finrank_hom_torPres_eq
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] (TA : Representation (ZMod p) Δ WA)
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0)
    (hιAΔ : ∀ (d : Δ) (w : WA), ιA (TA d w) = act d (ιA w)) :
    finrank (ZMod p) (N.linHom TA).invariants = finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants :=
  finrank_hom_eq_of_equiv N _ _ (torPresEquiv ιA hιA hranA) (fun d w => Subtype.ext (hιAΔ d w))

private theorem finiteDimensional_tor_of_pres
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] [FiniteDimensional (ZMod p) WA]
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0) :
    FiniteDimensional (ZMod p) (tor A p) :=
  LinearEquiv.finiteDimensional (torPresEquiv ιA hιA hranA)

end Transfer
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

namespace PDevissage
section FiniteTransfer
variable {p : ℕ} [Fact p.Prime]

private theorem finite_of_finite_quotient {G : Type*} [AddCommGroup G] (H : AddSubgroup G) [Finite H]
    [Finite (G ⧸ H)] : Finite G := by
  classical
  let s : G ⧸ H → G := Quotient.out
  have hs : ∀ x : G ⧸ H, (QuotientAddGroup.mk (s x) : G ⧸ H) = x := fun x => QuotientAddGroup.out_eq' x
  have hmem : ∀ g : G, g - s (QuotientAddGroup.mk g) ∈ H := fun g => by
    rw [← QuotientAddGroup.eq_iff_sub_mem, hs]
  refine Finite.of_injective
    (fun g : G => ((QuotientAddGroup.mk g : G ⧸ H), (⟨g - s (QuotientAddGroup.mk g), hmem g⟩ : H))) ?_
  intro g g' h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact sub_left_injective h2

variable {A : Type*} [AddCommGroup A] (B : AddSubgroup A)

private theorem finite_quot_of_finite [Finite (B ⧸ pmul B p)] [Finite ((A ⧸ B) ⧸ pmul (A ⧸ B) p)] :
    Finite (A ⧸ pmul A p) := by
  let K : AddSubgroup (A ⧸ pmul A p) := (Qq (p := p) B).toAddMonoidHom.ker
  haveI : Finite K := by
    have hK : (K : Set (A ⧸ pmul A p)) = Set.range (Qi (p := p) B) := by
      ext x
      exact exact_Qi_Qq B x
    have hfin : (Set.range (Qi (p := p) B)).Finite := Set.finite_range _
    rw [← hK] at hfin
    exact Set.finite_coe_iff.mpr hfin
  haveI : Finite ((A ⧸ pmul A p) ⧸ K) :=
    Finite.of_injective _ (QuotientAddGroup.kerLift_injective (Qq (p := p) B).toAddMonoidHom)
  exact finite_of_finite_quotient K

private theorem finite_tor_of_finite [Finite (tor B p)] [Finite (tor (A ⧸ B) p)] : Finite (tor A p) := by
  let K : AddSubgroup (tor A p) := (Tq (p := p) B).toAddMonoidHom.ker
  haveI : Finite K := by
    have hK : (K : Set (tor A p)) = Set.range (Ti (p := p) B) := by
      ext x
      exact exact_Ti_Tq B x
    have hfin : (Set.range (Ti (p := p) B)).Finite := Set.finite_range _
    rw [← hK] at hfin
    exact Set.finite_coe_iff.mpr hfin
  haveI : Finite ((tor A p) ⧸ K) :=
    Finite.of_injective _ (QuotientAddGroup.kerLift_injective (Tq (p := p) B).toAddMonoidHom)
  exact finite_of_finite_quotient K

private theorem Ti_bijective_of_subsingleton [Subsingleton (tor (A ⧸ B) p)] : Function.Bijective (Ti (p := p) B) := by
  refine ⟨Ti_injective B, fun x => ?_⟩
  exact (exact_Ti_Tq B x).mp (Subsingleton.elim _ _)

private theorem Qi_injective_of_subsingleton [Subsingleton (tor (A ⧸ B) p)] : Function.Injective (Qi (p := p) B) := by
  intro x y h
  have : Qi (p := p) B (x - y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨c, hc⟩ := (exact_delta_Qi B _).mp this
  rw [Subsingleton.elim c 0, map_zero] at hc
  exact (sub_eq_zero.mp hc.symm)

end FiniteTransfer
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.PDevissage"

open PDevissage _root_.IsLocalRing _root_.Module.IsLocalRing in

set_option maxHeartbeats 2400000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {F : Type*} [Field F] (hqF : (q : F) ≠ 0) (actF : Δ →* (F ≃+* F))
    (Rs : ValuationSubring F) (act : Δ →* (Rs ≃+* Rs))
    (hact : ∀ (d : Δ) (x : Rs), ((act d x : Rs) : F) = actF d (x : F))
    {e m : ℕ} (he : Ideal.span {(q : Rs)} = maximalIdeal Rs ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal Rs ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits Rs m).map (powMonoidHom q) = principalUnits Rs (m + e))
    (hnotors : ∀ u ∈ principalUnits Rs m, u ^ q = 1 → u = 1) (hidxm : (principalUnits Rs m).FiniteIndex)
    (hidxme : (principalUnits Rs (m + e)).FiniteIndex)
    (Λ : AddSubgroup Rs) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : Rs), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)

    (v : Fˣ →* Multiplicative ℤ) (hv : Function.Surjective v)
    (hvker : ∀ x : Fˣ, v x = 1 ↔ ((x : F) ∈ Rs ∧ ((x⁻¹ : Fˣ) : F) ∈ Rs))
    (hvΔ : ∀ (d : Δ) (x : Fˣ), v (Units.map ((actF d : F ≃+* F) : F →* F) x) = v x)

    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod q) VPF] (PF : Representation (ZMod q) Δ VPF)
    (πF : Additive Fˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : Fˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : Fˣ, w ^ q = u)
    (hπFΔ : ∀ (d : Δ) (u : Fˣ), πF (Additive.ofMul (Units.map ((actF d : F ≃+* F) : F →* F) u)) = PF d (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod q) VTF] (TF : Representation (ZMod q) Δ VTF)
    (ιF : VTF →+ Additive Fˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : Fˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ q = 1)
    (hιFΔ : ∀ (d : Δ) (w : VTF), Additive.toMul (ιF (TF d w)) = Units.map ((actF d : F ≃+* F) : F →* F) (Additive.toMul (ιF w))) :
    finrank (ZMod q) (N.linHom PF).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom TF).invariants
        + finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants := by
  classical
  haveI : Invertible (Fintype.card Δ : ZMod q) := by
    apply invertibleOfNonzero
    intro h
    exact hΔ ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hunit : IsUnit ((Fintype.card Δ : ZMod q)) := isUnit_of_invertible _
  have hqR : (q : Rs) ≠ 0 := fun h => hqF (by
    have := congrArg (fun x : Rs => (x : F)) h
    simpa using this)

  have hinvF : ∀ (d : Δ) (x : F), actF d⁻¹ (actF d x) = x := fun d x => by
    have h := RingEquiv.congr_fun (map_mul actF d⁻¹ d) x
    rw [inv_mul_cancel, map_one] at h
    exact h.symm
  have hinvF' : ∀ (d : Δ) (x : F), actF d (actF d⁻¹ x) = x := fun d x => by
    simpa using hinvF d⁻¹ x
  have hinv : ∀ (d : Δ) (x : Rs), act d⁻¹ (act d x) = x := fun d x => by
    have h := RingEquiv.congr_fun (map_mul act d⁻¹ d) x
    rw [inv_mul_cancel, map_one] at h
    exact h.symm
  have hinv' : ∀ (d : Δ) (x : Rs), act d (act d⁻¹ x) = x := fun d x => by
    simpa using hinv d⁻¹ x

  let ψF : Δ → (Fˣ ≃* Fˣ) := fun d =>
    { toFun := fun u => Units.map ((actF d : F ≃+* F) : F →* F) u
      invFun := fun u => Units.map ((actF d⁻¹ : F ≃+* F) : F →* F) u
      left_inv := fun u => Units.ext (hinvF d _)
      right_inv := fun u => Units.ext (hinvF' d _)
      map_mul' := fun u v => map_mul _ _ _ }
  let actXF : Δ →* AddAut (Additive Fˣ) :=
    { toFun := fun d => MulEquiv.toAdditive (ψF d)
      map_one' := by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (ψF 1 u) = Additive.ofMul u
        congr 1
        apply Units.ext
        show actF 1 (u : F) = (u : F)
        rw [map_one]; rfl
      map_mul' := fun d d' => by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (ψF (d * d') u) = Additive.ofMul (ψF d (ψF d' u))
        congr 1
        apply Units.ext
        show actF (d * d') (u : F) = actF d (actF d' (u : F))
        rw [map_mul]; rfl }
  have actXF_apply : ∀ (d : Δ) (u : Fˣ),
      actXF d (Additive.ofMul u) = Additive.ofMul (Units.map ((actF d : F ≃+* F) : F →* F) u) := fun _ _ => rfl

  let ψR : Δ → (Rsˣ ≃* Rsˣ) := fun d =>
    { toFun := fun u => Units.map ((act d : Rs ≃+* Rs) : Rs →* Rs) u
      invFun := fun u => Units.map ((act d⁻¹ : Rs ≃+* Rs) : Rs →* Rs) u
      left_inv := fun u => Units.ext (hinv d _)
      right_inv := fun u => Units.ext (hinv' d _)
      map_mul' := fun u v => map_mul _ _ _ }
  let actXR : Δ →* AddAut (Additive Rsˣ) :=
    { toFun := fun d => MulEquiv.toAdditive (ψR d)
      map_one' := by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (ψR 1 u) = Additive.ofMul u
        congr 1
        apply Units.ext
        show act 1 (u : Rs) = (u : Rs)
        rw [map_one]; rfl
      map_mul' := fun d d' => by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (ψR (d * d') u) = Additive.ofMul (ψR d (ψR d' u))
        congr 1
        apply Units.ext
        show act (d * d') (u : Rs) = act d (act d' (u : Rs))
        rw [map_mul]; rfl }
  have actXR_apply : ∀ (d : Δ) (u : Rsˣ),
      actXR d (Additive.ofMul u) = Additive.ofMul (Units.map ((act d : Rs ≃+* Rs) : Rs →* Rs) u) := fun _ _ => rfl

  let Bm : AddSubgroup (Additive Rsˣ) := (principalUnits Rs m).toAddSubgroup
  haveI : Bm.FiniteIndex := by
    constructor
    rw [Subgroup.index_toAddSubgroup]
    exact hidxm.1
  have hpmulBm : ∀ x : Bm, x ∈ pmul Bm q ↔ Additive.toMul (x : Additive Rsˣ) ∈ principalUnits Rs (m + e) := by
    rintro ⟨a, ha⟩
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    rw [mem_pmul, ← hpow, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨a', ha'⟩, h⟩
      obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = a' := ⟨Additive.toMul a', rfl⟩
      refine ⟨w, ha', ?_⟩
      have := congrArg (fun x : Bm => Additive.toMul (x : Additive Rsˣ)) h
      simpa using this
    · rintro ⟨w, hw, hwu⟩
      refine ⟨⟨Additive.ofMul w, hw⟩, Subtype.ext ?_⟩
      show q • Additive.ofMul w = Additive.ofMul u
      rw [← ofMul_pow]
      exact congrArg Additive.ofMul hwu
  haveI : (pmul Bm q).FiniteIndex := by
    have : pmul Bm q = (principalUnits Rs (m + e)).toAddSubgroup.addSubgroupOf Bm := by
      ext x
      rw [hpmulBm, AddSubgroup.mem_addSubgroupOf]
      rfl
    rw [this]
    haveI : (principalUnits Rs (m + e)).toAddSubgroup.FiniteIndex := by
      constructor
      rw [Subgroup.index_toAddSubgroup]
      exact hidxme.1
    infer_instance
  haveI : Finite (Bm ⧸ pmul Bm q) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : Finite (Additive Rsˣ ⧸ Bm) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : Subsingleton (tor Bm q) := by
    refine ⟨fun x y => ?_⟩
    have hx1 : ∀ z : tor Bm q, z = 0 := by
      rintro ⟨⟨a, ha⟩, hz⟩
      obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      have hq1 : u ^ q = 1 := by
        have := congrArg (fun x : Bm => Additive.toMul (x : Additive Rsˣ)) (mem_tor.mp hz)
        simpa using this
      have := hnotors u ha hq1
      subst this
      rfl
    rw [hx1 x, hx1 y]
  haveI : Finite (tor Bm q) := Finite.of_subsingleton
  haveI : Finite (Additive Rsˣ ⧸ pmul (Additive Rsˣ) q) := finite_quot_of_finite Bm
  haveI : Finite (tor (Additive Rsˣ) q) := finite_tor_of_finite Bm
  haveI : FiniteDimensional (ZMod q) (Additive Rsˣ ⧸ pmul (Additive Rsˣ) q) := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod q) (tor (Additive Rsˣ) q) := Module.Finite.of_finite
  have hcanR : ∀ a : Additive Rsˣ, (QuotientAddGroup.mk' (pmul (Additive Rsˣ) q)) a = 0 ↔ a ∈ pmul (Additive Rsˣ) q :=
    fun a => QuotientAddGroup.eq_zero_iff a
  have hU := IsLocalRing.finrank_invariants_linHom_units_modPow_eq hΔ hqR act he hem hfin hpow hnotors hidxm hidxme
    Λ hΛ PΛ πΛ hπΛ hkerΛ hπΛΔ b hb N
    (quotRep actXR) (QuotientAddGroup.mk' _) (QuotientAddGroup.mk'_surjective _)
    (fun u => by
      rw [hcanR, mem_pmul]
      constructor
      · rintro ⟨a', ha'⟩
        obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = a' := ⟨Additive.toMul a', rfl⟩
        exact ⟨w, Additive.ofMul.injective (by rw [ofMul_pow]; exact ha')⟩
      · rintro ⟨w, hw⟩; exact ⟨Additive.ofMul w, by rw [← ofMul_pow, hw]⟩)
    (fun d u => rfl)
    (torRep actXR) ((tor (Additive Rsˣ) q).subtype) (fun x y h => Subtype.ext h)
    (fun u => by
      constructor
      · rintro ⟨z, hz⟩
        change (z : Additive Rsˣ) = Additive.ofMul u at hz
        have := mem_tor.mp z.2
        rw [hz, ← ofMul_pow, ← ofMul_one, Additive.ofMul.injective.eq_iff] at this
        exact this
      · intro h
        exact ⟨⟨Additive.ofMul u, mem_tor.mpr (by rw [← ofMul_pow, h, ofMul_one])⟩, rfl⟩)
    (fun d w => rfl)

  let B : AddSubgroup (Additive Fˣ) := (MonoidHom.ker v).toAddSubgroup
  have hBmem : ∀ x : Fˣ, Additive.ofMul x ∈ B ↔ v x = 1 := fun x => MonoidHom.mem_ker
  have hB : ∀ (d : Δ) (a : Additive Fˣ), a ∈ B → actXF d a ∈ B := by
    intro d a ha
    obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
    rw [actXF_apply, hBmem, hvΔ]
    exact (hBmem x).mp ha
  have hjmem : ∀ u : Rsˣ, Additive.ofMul (Units.map ((algebraMap Rs F : Rs →+* F) : Rs →* F) u) ∈ B := fun u => by
    rw [hBmem, hvker]
    refine ⟨(u : Rs).2, ?_⟩
    rw [Units.coe_map_inv]
    exact ((u⁻¹ : Rsˣ) : Rs).2
  let j : Additive Rsˣ →+ B :=
    { toFun := fun a => ⟨Additive.ofMul (Units.map ((algebraMap Rs F : Rs →+* F) : Rs →* F) (Additive.toMul a)), hjmem _⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a a' => Subtype.ext (by
        show Additive.ofMul (Units.map ((algebraMap Rs F : Rs →+* F) : Rs →* F) (Additive.toMul (a + a')))
          = Additive.ofMul _ + Additive.ofMul _
        rw [← ofMul_mul, ← map_mul]
        rfl) }
  have hj_apply : ∀ u : Rsˣ, ((j (Additive.ofMul u) : B) : Additive Fˣ)
      = Additive.ofMul (Units.map ((algebraMap Rs F : Rs →+* F) : Rs →* F) u) := fun _ => rfl
  have hj_val : ∀ u : Rsˣ, ((Additive.toMul ((j (Additive.ofMul u) : B) : Additive Fˣ) : Fˣ) : F) = ((u : Rs) : F) :=
    fun _ => rfl
  have hj_inj : Function.Injective j := by
    intro a a' h
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    obtain ⟨u', rfl⟩ : ∃ u', Additive.ofMul u' = a' := ⟨Additive.toMul a', rfl⟩
    have hval : ((u : Rs) : F) = ((u' : Rs) : F) :=
      congrArg (fun b : B => ((Additive.toMul (b : Additive Fˣ) : Fˣ) : F)) h
    congr 1
    exact Units.ext (Subtype.ext hval)
  have hj_surj : Function.Surjective j := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
    obtain ⟨hx, hx'⟩ := (hvker x).mp ((hBmem x).mp ha)
    let u : Rsˣ := ⟨⟨x, hx⟩, ⟨((x⁻¹ : Fˣ) : F), hx'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
    refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
    show Additive.ofMul (Units.map _ u) = Additive.ofMul x
    exact congrArg Additive.ofMul (Units.ext rfl)
  let jE : Additive Rsˣ ≃+ B := AddEquiv.ofBijective j ⟨hj_inj, hj_surj⟩
  have hjE : ∀ a, jE a = j a := fun _ => rfl
  have hj_equiv : ∀ (d : Δ) (a : Additive Rsˣ), j (actXR d a) = subAct actXF B hB d (j a) := by
    intro d a
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    apply Subtype.ext
    rw [actXR_apply, hj_apply, coe_subAct, hj_apply, actXF_apply]
    congr 1
    apply Units.ext
    exact hact d (u : Rs)

  have hcanB : ∀ z : B, (QuotientAddGroup.mk' (pmul B q)) z = 0 ↔ z ∈ pmul B q :=
    fun z => QuotientAddGroup.eq_zero_iff z
  let πB : Additive Rsˣ →+ B ⧸ pmul B q := (QuotientAddGroup.mk' (pmul B q)).comp j
  have hπB : ∀ a, πB a = (QuotientAddGroup.mk' (pmul B q)) (j a) := fun _ => rfl
  have hπB_surj : Function.Surjective πB := (QuotientAddGroup.mk'_surjective (pmul B q)).comp hj_surj
  have hπB_ker : ∀ a, πB a = 0 ↔ ∃ a', q • a' = a := by
    intro a
    rw [hπB, hcanB, mem_pmul]
    constructor
    · rintro ⟨b', hb'⟩
      obtain ⟨a', rfl⟩ := hj_surj b'
      exact ⟨a', hj_inj (by rw [map_nsmul]; exact hb')⟩
    · rintro ⟨a', rfl⟩
      exact ⟨j a', (map_nsmul j q a').symm⟩
  have hQB : finrank (ZMod q) (N.linHom (quotRep (p := q) (subAct actXF B hB))).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) actXR)).invariants :=
    finrank_hom_quotPres_eq N actXR _ πB hπB_surj hπB_ker (fun d a => by
      rw [hπB, hπB, hj_equiv]; rfl)
  let ιB : tor B q →+ Additive Rsˣ := jE.symm.toAddMonoidHom.comp (tor B q).subtype
  have hιB : ∀ z : tor B q, j (ιB z) = (z : B) := fun z => by
    show jE (jE.symm _) = _
    exact jE.apply_symm_apply _
  have hιB_inj : Function.Injective ιB := by
    intro z z' h
    apply Subtype.ext
    rw [← hιB z, ← hιB z', h]
  have hιB_ran : ∀ a, a ∈ Set.range ιB ↔ q • a = 0 := by
    intro a
    constructor
    · rintro ⟨z, rfl⟩
      apply hj_inj
      rw [map_nsmul, hιB, map_zero]
      exact_mod_cast mem_tor.mp z.2
    · intro ha
      refine ⟨⟨j a, mem_tor.mpr (by rw [← map_nsmul, ha, map_zero])⟩, hj_inj ?_⟩
      rw [hιB]
  have hTB : finrank (ZMod q) (N.linHom (torRep (p := q) (subAct actXF B hB))).invariants
      = finrank (ZMod q) (N.linHom (torRep (p := q) actXR)).invariants :=
    finrank_hom_torPres_eq N actXR _ ιB hιB_inj hιB_ran (fun d z => hj_inj (by
      rw [hιB, hj_equiv, hιB]; rfl))
  haveI : FiniteDimensional (ZMod q) (B ⧸ pmul B q) :=
    finiteDimensional_quot_of_pres ((QuotientAddGroup.mk' (pmul (Additive Rsˣ) q)).comp jE.symm.toAddMonoidHom)
      ((QuotientAddGroup.mk'_surjective (pmul (Additive Rsˣ) q)).comp jE.symm.surjective) (fun z => by
        rw [AddMonoidHom.comp_apply, hcanR, mem_pmul]
        constructor
        · rintro ⟨a', ha'⟩
          refine ⟨jE a', jE.symm.injective ?_⟩
          rw [map_nsmul, AddEquiv.symm_apply_apply]
          exact ha'
        · rintro ⟨z', rfl⟩
          exact ⟨jE.symm z', by rw [map_nsmul]; rfl⟩)
  haveI : FiniteDimensional (ZMod q) (tor B q) :=
    finiteDimensional_tor_of_pres (j.comp (tor (Additive Rsˣ) q).subtype)
      (hj_inj.comp (fun x y h => Subtype.ext h)) (fun z => by
        constructor
        · rintro ⟨a, rfl⟩
          show q • j ((tor (Additive Rsˣ) q).subtype a) = 0
          rw [← map_nsmul]
          have h0 : q • ((tor (Additive Rsˣ) q).subtype a) = 0 := mem_tor.mp a.2
          rw [h0, map_zero]
        · intro hz
          obtain ⟨a, rfl⟩ := hj_surj z
          refine ⟨⟨a, mem_tor.mpr (hj_inj ?_)⟩, rfl⟩
          rw [map_nsmul, hz, map_zero])

  let vA : Additive Fˣ →+ ℤ :=
    { toFun := fun a => Multiplicative.toAdd (v (Additive.toMul a))
      map_zero' := by simp
      map_add' := fun a a' => by
        show Multiplicative.toAdd (v (Additive.toMul a * Additive.toMul a')) = _
        rw [map_mul, toAdd_mul] }
  have hvA : ∀ x : Fˣ, vA (Additive.ofMul x) = Multiplicative.toAdd (v x) := fun _ => rfl
  have hvA_surj : Function.Surjective vA := fun n => by
    obtain ⟨x, hx⟩ := hv (Multiplicative.ofAdd n)
    exact ⟨Additive.ofMul x, by rw [hvA, hx]; rfl⟩
  have hle : B ≤ vA.ker := by
    intro a ha
    obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
    rw [AddMonoidHom.mem_ker, hvA, (hBmem x).mp ha]
    rfl
  let w : Additive Fˣ ⧸ B →+ ℤ := QuotientAddGroup.lift B vA hle
  have hw : ∀ a, w (QuotientAddGroup.mk a) = vA a := fun _ => rfl
  have hw_inj : Function.Injective w := by
    intro x y h
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      induction y using QuotientAddGroup.induction_on with
      | H a' =>
        rw [hw, hw] at h
        rw [QuotientAddGroup.eq]
        obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
        obtain ⟨x', rfl⟩ : ∃ x', Additive.ofMul x' = a' := ⟨Additive.toMul a', rfl⟩
        rw [← ofMul_inv, ← ofMul_mul, hBmem, map_mul, map_inv]
        rw [hvA, hvA] at h
        have : v x = v x' := Multiplicative.toAdd.injective h
        rw [this, inv_mul_cancel]
  have hw_surj : Function.Surjective w := fun n => by
    obtain ⟨a, ha⟩ := hvA_surj n
    exact ⟨QuotientAddGroup.mk a, by rw [hw, ha]⟩

  haveI : Subsingleton (tor (Additive Fˣ ⧸ B) q) := by
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ z : tor (Additive Fˣ ⧸ B) q, z = 0 := by
      intro z
      apply Subtype.ext
      apply hw_inj
      rw [ZeroMemClass.coe_zero, map_zero]
      have := congrArg w (mem_tor.mp z.2)
      rw [map_nsmul, map_zero, nsmul_eq_mul, mul_eq_zero] at this
      exact this.resolve_left (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
    rw [h0 x, h0 y]

  have htrivC : ∀ (d : Δ) (c : Additive Fˣ ⧸ B), quotAct actXF B hB d c = c := by
    intro d c
    induction c using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
      rw [quotAct_mk, QuotientAddGroup.eq, actXF_apply, ← ofMul_inv, ← ofMul_mul, hBmem, map_mul, map_inv, hvΔ,
        inv_mul_cancel]

  haveI : (pmul (Additive Fˣ ⧸ B) q).Normal := ⟨fun n hn g => by rwa [add_comm g n, add_neg_cancel_right]⟩
  have hcanC : ∀ c : (Additive Fˣ ⧸ B), (QuotientAddGroup.mk' (pmul (Additive Fˣ ⧸ B) q)) c = 0 ↔ c ∈ pmul (Additive Fˣ ⧸ B) q :=
    fun c => QuotientAddGroup.eq_zero_iff c
  have hleC : pmul (Additive Fˣ ⧸ B) q ≤ ((Int.castAddHom (ZMod q)).comp w).ker := by
    rintro _ ⟨c, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show ((Int.castAddHom (ZMod q)).comp w) (q • c) = 0
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let wq : (Additive Fˣ ⧸ B) ⧸ pmul (Additive Fˣ ⧸ B) q →+ ZMod q := QuotientAddGroup.lift (pmul (Additive Fˣ ⧸ B) q) ((Int.castAddHom (ZMod q)).comp w) hleC
  have hwq : ∀ c : (Additive Fˣ ⧸ B), wq (QuotientAddGroup.mk c) = ((w c : ℤ) : ZMod q) := fun _ => rfl
  have hwq_surj : Function.Surjective wq := fun z => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    obtain ⟨c, rfl⟩ := hw_surj n
    exact ⟨QuotientAddGroup.mk c, rfl⟩
  have hwq_inj : Function.Injective wq := by
    intro x y h
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      induction y using QuotientAddGroup.induction_on with
      | H c' =>
        rw [hwq, hwq] at h
        rw [QuotientAddGroup.eq, mem_pmul]
        have hdvd : (q : ℤ) ∣ w (-c + c') := by
          rw [map_add, map_neg, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_neg, h, neg_add_cancel]
        obtain ⟨k, hk⟩ := hdvd
        obtain ⟨c₀, hc₀⟩ := hw_surj k
        refine ⟨c₀, hw_inj ?_⟩
        rw [map_nsmul, hc₀, hk, nsmul_eq_mul]
  let L : ((Additive Fˣ ⧸ B) ⧸ pmul (Additive Fˣ ⧸ B) q) ≃ₗ[ZMod q] ZMod q :=
    LinearEquiv.ofBijective (wq.toZModLinearMap q) ⟨hwq_inj, hwq_surj⟩
  have hQC : finrank (ZMod q) (N.linHom (quotRep (p := q) (quotAct actXF B hB))).invariants
      = finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants :=
    finrank_hom_eq_of_equiv N _ _ L (fun d z => by
      induction z using QuotientAddGroup.induction_on with
      | H c =>
        show L (QuotientAddGroup.mk (quotAct actXF B hB d c)) = L (QuotientAddGroup.mk c)
        rw [htrivC])
  haveI : FiniteDimensional (ZMod q) ((Additive Fˣ ⧸ B) ⧸ pmul (Additive Fˣ ⧸ B) q) := LinearEquiv.finiteDimensional L.symm

  haveI : Finite (B ⧸ pmul B q) := Module.finite_of_finite (ZMod q)
  haveI : Finite ((Additive Fˣ ⧸ B) ⧸ pmul (Additive Fˣ ⧸ B) q) := Module.finite_of_finite (ZMod q)
  haveI : Finite (Additive Fˣ ⧸ pmul (Additive Fˣ) q) := finite_quot_of_finite B
  haveI : FiniteDimensional (ZMod q) (Additive Fˣ ⧸ pmul (Additive Fˣ) q) := Module.Finite.of_finite
  have hT3a := Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card hunit N
    (quotRep (p := q) (subAct actXF B hB)) (quotRep (p := q) actXF) (quotRep (p := q) (quotAct actXF B hB))
    (Qi B) (Qq B) (Qi_equivariant actXF B hB) (Qq_equivariant actXF B hB)
    (Qi_injective_of_subsingleton B) (Qq_surjective B) (exact_Qi_Qq B)
  let eT : tor B q ≃ₗ[ZMod q] tor (Additive Fˣ) q := LinearEquiv.ofBijective (Ti B) (Ti_bijective_of_subsingleton B)
  have hTA : finrank (ZMod q) (N.linHom (torRep (p := q) (subAct actXF B hB))).invariants
      = finrank (ZMod q) (N.linHom (torRep (p := q) actXF)).invariants :=
    finrank_hom_eq_of_equiv N _ _ eT (fun d z => LinearMap.congr_fun (Ti_equivariant (p := q) actXF B hB d) z)

  have hPF : finrank (ZMod q) (N.linHom PF).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) actXF)).invariants := by
    refine finrank_hom_quotPres_eq N actXF PF πF hπF (fun a => ?_) (fun d a => ?_)
    · obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      rw [hkerπF]
      constructor
      · rintro ⟨w', hw'⟩; exact ⟨Additive.ofMul w', by rw [← ofMul_pow, hw']⟩
      · rintro ⟨a', ha'⟩
        obtain ⟨w', rfl⟩ : ∃ w', Additive.ofMul w' = a' := ⟨Additive.toMul a', rfl⟩
        exact ⟨w', Additive.ofMul.injective (by rw [ofMul_pow]; exact ha')⟩
    · obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      exact hπFΔ d u
  have hTF : finrank (ZMod q) (N.linHom TF).invariants
      = finrank (ZMod q) (N.linHom (torRep (p := q) actXF)).invariants := by
    refine finrank_hom_torPres_eq N actXF TF ιF hιF (fun a => ?_) (fun d w' => ?_)
    · obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      rw [hranιF, ← ofMul_pow, ← ofMul_one, Additive.ofMul.injective.eq_iff]
    · apply Additive.toMul.injective
      rw [hιFΔ]
      rfl
  linarith

end S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq
end P2MW
export P2MW.S_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq (solution)
