-- Prove2me | solution 1 for IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1030f9c1-1e68-5c84-a06b-7b4f088dfa75

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
import Theorems.Thm_Representation_finrank_invariants_linHom_of_basis_regular
import Theorems.Thm_IsLocalRing_coe_mul_sub_one_sub_mem_maximalIdeal_pow
import Theorems.Thm_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq
import Theorems.Thm_IsLocalRing_map_ringEquiv_mem_principalUnits_iff
import Theorems.Thm_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

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
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.PDevissage"

open PDevissage _root_.IsLocalRing _root_.Module.IsLocalRing in

set_option maxHeartbeats 2400000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (hqR : (q : R) ≠ 0)
    (act : Δ →* (R ≃+* R))
    {e m : ℕ} (he : Ideal.span {(q : R)} = maximalIdeal R ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal R ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits R m).map (powMonoidHom q) = principalUnits R (m + e))
    (Λ : AddSubgroup R) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : R), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)
    {VU : Type*} [AddCommGroup VU] [Module (ZMod q) VU] (PU : Representation (ZMod q) Δ VU)
    (πU : Additive (principalUnits R m) →+ VU) (hπU : Function.Surjective πU)
    (hkerU : ∀ u : principalUnits R m,
      πU (Additive.ofMul u) = 0 ↔ ∃ v : principalUnits R m, v ^ q = u)
    (hπUΔ : ∀ (d : Δ) (u : principalUnits R m) (hu : Units.map ((act d : R ≃+* R) : R →* R) (u : Rˣ) ∈ principalUnits R m),
      πU (Additive.ofMul ⟨Units.map ((act d : R ≃+* R) : R →* R) u, hu⟩) = PU d (πU (Additive.ofMul u))) :
    finrank (ZMod q) (N.linHom PU).invariants = Fintype.card ι * finrank (ZMod q) VN := by
  classical
  haveI : Invertible (Fintype.card Δ : ZMod q) := by
    apply invertibleOfNonzero
    intro h
    exact hΔ ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hm1 : 1 ≤ m := by omega

  have htf : ∀ a : R, q • a = 0 → a = 0 := fun a h => by
    rw [nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hqR

  have hinv : ∀ (d : Δ) (x : R), act d⁻¹ (act d x) = x := fun d x => by
    have h := RingEquiv.congr_fun (map_mul act d⁻¹ d) x
    rw [inv_mul_cancel, map_one] at h
    exact h.symm
  have hinv' : ∀ (d : Δ) (x : R), act d (act d⁻¹ x) = x := fun d x => by
    simpa using hinv d⁻¹ x
  let actR : Δ →* AddAut R :=
    { toFun := fun d => (act d : R ≃+* R).toAddEquiv
      map_one' := by ext x; simp
      map_mul' := fun d d' => by
        ext x
        show act (d * d') x = act d (act d' x)
        rw [map_mul]
        rfl }
  have actR_apply : ∀ (d : Δ) (x : R), actR d x = act d x := fun _ _ => rfl

  let M : AddSubgroup R := (maximalIdeal R ^ m).toAddSubgroup
  have hM : ∀ (d : Δ) (x : R), x ∈ M → actR d x ∈ M := fun d x hx =>
    (map_ringEquiv_mem_maximalIdeal_pow_iff (act d)).mpr hx
  haveI : M.FiniteIndex := hfin m

  have hqmul : ∀ x : R, x ∈ maximalIdeal R ^ (m + e) ↔ ∃ y ∈ maximalIdeal R ^ m, x = q * y := by
    intro x
    rw [pow_add, ← he, mul_comm, Ideal.mem_span_singleton_mul]
    constructor
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, h.symm⟩
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, h.symm⟩
  have hpmulM : ∀ z : M, z ∈ pmul M q ↔ (z : R) ∈ maximalIdeal R ^ (m + e) := by
    intro z
    rw [mem_pmul, hqmul]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, y.2, ?_⟩
      have := congrArg Subtype.val hy
      simp only [AddSubgroupClass.coe_nsmul, nsmul_eq_mul] at this
      exact this.symm
    · rintro ⟨y, hy, hzy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simp only [AddSubgroupClass.coe_nsmul, nsmul_eq_mul]; exact hzy.symm)⟩

  have hsub : ∀ u : principalUnits R m, ((u : Rˣ) : R) - 1 ∈ M := fun u => u.2
  let ω₀ : principalUnits R m → M ⧸ pmul M q := fun u => QuotientAddGroup.mk ⟨((u : Rˣ) : R) - 1, hsub u⟩
  have hω_one : ω₀ 1 = 0 := by
    show QuotientAddGroup.mk _ = 0
    rw [QuotientAddGroup.eq_zero_iff, hpmulM]
    simp
  have hω_mul : ∀ u v : principalUnits R m, ω₀ (u * v) = ω₀ u + ω₀ v := by
    intro u v
    show QuotientAddGroup.mk _ = QuotientAddGroup.mk _ + QuotientAddGroup.mk _
    rw [← QuotientAddGroup.mk_add, eq_comm, QuotientAddGroup.eq, hpmulM]
    have hdef := coe_mul_sub_one_sub_mem_maximalIdeal_pow (u := (u : Rˣ)) (v := (v : Rˣ)) u.2 v.2
    have hle : maximalIdeal R ^ (2 * m) ≤ maximalIdeal R ^ (m + e) := Ideal.pow_le_pow_right (by omega)
    have hneg := hle hdef

    have hcoe : (((-(⟨((u : Rˣ) : R) - 1, hsub u⟩ + ⟨((v : Rˣ) : R) - 1, hsub v⟩) +
        ⟨(((u * v : principalUnits R m) : Rˣ) : R) - 1, hsub (u * v)⟩ : M) : M) : R)
        = (((u : Rˣ) * (v : Rˣ) : Rˣ) : R) - 1 - ((((u : Rˣ) : R) - 1) + (((v : Rˣ) : R) - 1)) := by
      push_cast
      ring
    rw [hcoe]
    exact hneg
  let ω : Additive (principalUnits R m) →+ M ⧸ pmul M q :=
    { toFun := fun u => ω₀ (Additive.toMul u)
      map_zero' := hω_one
      map_add' := fun u v => hω_mul (Additive.toMul u) (Additive.toMul v) }
  have hω_apply : ∀ u : principalUnits R m, ω (Additive.ofMul u) = ω₀ u := fun _ => rfl
  have hω_surj : Function.Surjective ω := by
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨u, hu, huy⟩ := exists_mem_principalUnits_coe_sub_one_eq hm1 y.2
      refine ⟨Additive.ofMul ⟨u, hu⟩, ?_⟩
      rw [hω_apply]
      show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
      congr 1
      exact Subtype.ext huy
  have hω_ker : ∀ a : Additive (principalUnits R m), ω a = 0 ↔ ∃ a', q • a' = a := by
    intro a
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    rw [hω_apply]
    show QuotientAddGroup.mk _ = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, hpmulM]
    change ((u : Rˣ) : R) - 1 ∈ maximalIdeal R ^ (m + e) ↔ _
    rw [← mem_principalUnits_iff, ← hpow, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      refine ⟨Additive.ofMul ⟨v, hv⟩, ?_⟩
      rw [← ofMul_pow]
      congr 1
      exact Subtype.ext (by simpa using hvu)
    · rintro ⟨a', ha'⟩
      obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = a' := ⟨Additive.toMul a', rfl⟩
      rw [← ofMul_pow] at ha'
      have hvu : v ^ q = u := Additive.ofMul.injective ha'
      exact ⟨v, v.2, by rw [powMonoidHom_apply]; exact congrArg (fun w : principalUnits R m => (w : Rˣ)) hvu⟩

  let φ : Δ → (principalUnits R m ≃* principalUnits R m) := fun d =>
    { toFun := fun u => ⟨Units.map ((act d : R ≃+* R) : R →* R) u,
        (map_ringEquiv_mem_principalUnits_iff (act d) (u := (u : Rˣ))).mpr u.2⟩
      invFun := fun u => ⟨Units.map ((act d⁻¹ : R ≃+* R) : R →* R) u,
        (map_ringEquiv_mem_principalUnits_iff (act d⁻¹) (u := (u : Rˣ))).mpr u.2⟩
      left_inv := fun u => Subtype.ext (Units.ext (hinv d _))
      right_inv := fun u => Subtype.ext (Units.ext (hinv' d _))
      map_mul' := fun u v => Subtype.ext (map_mul _ _ _) }
  have hφ_coe : ∀ (d : Δ) (u : principalUnits R m), (((φ d u : principalUnits R m) : Rˣ) : R) = act d ((u : Rˣ) : R) :=
    fun _ _ => rfl
  let actU : Δ →* AddAut (Additive (principalUnits R m)) :=
    { toFun := fun d => MulEquiv.toAdditive (φ d)
      map_one' := by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (φ 1 u) = Additive.ofMul u
        congr 1
        apply Subtype.ext; apply Units.ext
        show act 1 ((u : Rˣ) : R) = ((u : Rˣ) : R)
        rw [map_one]; rfl
      map_mul' := fun d d' => by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (φ (d * d') u) = Additive.ofMul (φ d (φ d' u))
        congr 1
        apply Subtype.ext; apply Units.ext
        show act (d * d') ((u : Rˣ) : R) = act d (act d' ((u : Rˣ) : R))
        rw [map_mul]; rfl }
  have actU_apply : ∀ (d : Δ) (u : principalUnits R m), actU d (Additive.ofMul u) = Additive.ofMul (φ d u) :=
    fun _ _ => rfl

  have h1 : finrank (ZMod q) (N.linHom PU).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) actU)).invariants := by
    refine finrank_hom_quotPres_eq N actU PU πU hπU (fun a => ?_) (fun d a => ?_)
    · obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      rw [hkerU]
      constructor
      · rintro ⟨v, hv⟩; exact ⟨Additive.ofMul v, by rw [← ofMul_pow, hv]⟩
      · rintro ⟨a', ha'⟩
        obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = a' := ⟨Additive.toMul a', rfl⟩
        exact ⟨v, Additive.ofMul.injective (by rw [ofMul_pow]; exact ha')⟩
    · obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      exact hπUΔ d u ((map_ringEquiv_mem_principalUnits_iff (act d) (u := (u : Rˣ))).mpr u.2)
  have h2 : finrank (ZMod q) (N.linHom (quotRep (p := q) (subAct actR M hM))).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) actU)).invariants := by
    refine finrank_hom_quotPres_eq N actU _ ω hω_surj hω_ker (fun d a => ?_)
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    rw [actU_apply, hω_apply, hω_apply]
    show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    congr 1
    apply Subtype.ext
    show act d ((u : Rˣ) : R) - 1 = act d (((u : Rˣ) : R) - 1)
    rw [map_sub, map_one]

  have hpmulR : pmul R q = (maximalIdeal R ^ e).toAddSubgroup := by
    ext x
    rw [mem_pmul, Submodule.mem_toAddSubgroup, ← he, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, by rw [nsmul_eq_mul, mul_comm]⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, by rw [nsmul_eq_mul, mul_comm]⟩
  haveI : (pmul R q).FiniteIndex := by rw [hpmulR]; exact hfin e
  haveI : Finite (R ⧸ pmul R q) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : FiniteDimensional (ZMod q) (R ⧸ pmul R q) := Module.Finite.of_finite
  have hpmulM' : pmul M q = (maximalIdeal R ^ (m + e)).toAddSubgroup.addSubgroupOf M := by
    ext z
    rw [hpmulM, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
  haveI : (pmul M q).FiniteIndex := by
    rw [hpmulM']
    haveI := hfin (m + e)
    infer_instance
  haveI : Finite (M ⧸ pmul M q) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : FiniteDimensional (ZMod q) (M ⧸ pmul M q) := Module.Finite.of_finite
  have hΛ' : ∀ (d : Δ) (x : R), x ∈ Λ → actR d x ∈ Λ := hΛ
  haveI : FiniteDimensional (ZMod q) (Λ ⧸ pmul Λ q) := finiteDimensional_quot_of_pres πΛ hπΛ hkerΛ

  have hcanR : ∀ a : R, (QuotientAddGroup.mk' (pmul R q)) a = 0 ↔ ∃ a', q • a' = a := fun a =>
    QuotientAddGroup.eq_zero_iff a
  have hcanM : ∀ z : M, (QuotientAddGroup.mk' (pmul M q)) z = 0 ↔ ∃ z', q • z' = z := fun z =>
    QuotientAddGroup.eq_zero_iff z
  have hcanΛ : ∀ z : Λ, (QuotientAddGroup.mk' (pmul Λ q)) z = 0 ↔ ∃ z', q • z' = z := fun z =>
    QuotientAddGroup.eq_zero_iff z

  have h3 : finrank (ZMod q) (N.linHom (quotRep (p := q) actR)).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) (subAct actR M hM))).invariants :=
    Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree hΔ actR htf M hM N
      (quotRep actR) (QuotientAddGroup.mk' _) (QuotientAddGroup.mk'_surjective _) hcanR (fun d a => rfl)
      (quotRep (subAct actR M hM)) (QuotientAddGroup.mk' _) (QuotientAddGroup.mk'_surjective _) hcanM
      (fun d z => rfl)

  have h4 : finrank (ZMod q) (N.linHom (quotRep (p := q) actR)).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) (subAct actR Λ hΛ'))).invariants :=
    Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree hΔ actR htf Λ hΛ' N
      (quotRep actR) (QuotientAddGroup.mk' _) (QuotientAddGroup.mk'_surjective _) hcanR (fun d a => rfl)
      (quotRep (subAct actR Λ hΛ')) (QuotientAddGroup.mk' _) (QuotientAddGroup.mk'_surjective _) hcanΛ
      (fun d z => rfl)

  have h5 : finrank (ZMod q) (N.linHom PΛ).invariants
      = finrank (ZMod q) (N.linHom (quotRep (p := q) (subAct actR Λ hΛ'))).invariants :=
    finrank_hom_quotPres_eq N (subAct actR Λ hΛ') PΛ πΛ hπΛ hkerΛ (fun d z => hπΛΔ d z)
  have h6 : finrank (ZMod q) (N.linHom PΛ).invariants = Fintype.card ι * finrank (ZMod q) VN :=
    Representation.finrank_invariants_linHom_of_basis_regular N PΛ b hb
  linarith

end S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank
end P2MW
export P2MW.S_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank (solution)
