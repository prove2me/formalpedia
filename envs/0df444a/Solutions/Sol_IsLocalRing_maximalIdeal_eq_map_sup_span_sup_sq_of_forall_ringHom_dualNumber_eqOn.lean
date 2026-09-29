-- Prove2me | solution 1 for IsLocalRing.maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f53fdbe5-85b1-5042-9473-323afca7488c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn

set_option autoImplicit false

open IsLocalRing TrivSqZeroExt

def DDTsep.dualHom {R k : Type} [CommRing R] [CommRing k] (res : R →+* k) (δ : R → k)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = res a * δ b + res b * δ a) :
    R →+* DualNumber k where
  toFun r := inl (res r) + inr (δ r)
  map_one' := by
    have h1 : δ 1 = 0 := by
      have := hmul 1 1
      rw [mul_one, map_one, one_mul] at this
      exact left_eq_add.mp this
    apply TrivSqZeroExt.ext <;> simp [h1]
  map_mul' := by
    intro a b
    apply TrivSqZeroExt.ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, zero_add, snd_mul, fst_add, fst_inl, fst_inr, add_zero, map_mul,
        hmul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by
    have h0 : δ 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    apply TrivSqZeroExt.ext <;> simp [h0]
  map_add' := by
    intro a b
    apply TrivSqZeroExt.ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, zero_add, map_add, hadd]

theorem DDTsep.dualHom_apply {R k : Type} [CommRing R] [CommRing k] (res : R →+* k) (δ : R → k)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = res a * δ b + res b * δ a) (r : R) :
    DDTsep.dualHom res δ hadd hmul r = inl (res r) + inr (δ r) := rfl

theorem DDTsep.fst_dualHom {R k : Type} [CommRing R] [CommRing k] (res : R →+* k) (δ : R → k)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = res a * δ b + res b * δ a) (r : R) :
    (DDTsep.dualHom res δ hadd hmul r).fst = res r := by simp [DDTsep.dualHom_apply]

theorem DDTsep.snd_dualHom {R k : Type} [CommRing R] [CommRing k] (res : R →+* k) (δ : R → k)
    (hadd : ∀ a b, δ (a + b) = δ a + δ b) (hmul : ∀ a b, δ (a * b) = res a * δ b + res b * δ a) (r : R) :
    (DDTsep.dualHom res δ hadd hmul r).snd = δ r := by simp [DDTsep.dualHom_apply]

namespace DDTsep

variable {O : Type} [CommRing O] [IsLocalRing O]
variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]

theorem res_surjective (res : R →+* ResidueField O) (hres : res.comp (algebraMap O R) = residue O) :
    Function.Surjective res := by
  intro y
  obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨algebraMap O R o, by rw [← RingHom.comp_apply, hres]⟩

theorem ker_res (res : R →+* ResidueField O) (hres : res.comp (algebraMap O R) = residue O) :
    RingHom.ker res = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res (res_surjective res hres))

theorem mem_maximalIdeal_iff (res : R →+* ResidueField O) (hres : res.comp (algebraMap O R) = residue O)
    (x : R) : x ∈ maximalIdeal R ↔ res x = 0 := by
  rw [← ker_res res hres, RingHom.mem_ker]

end DDTsep

open DDTsep in
theorem solution
    (O : Type) [CommRing O] [IsLocalRing O]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    (res : R →+* IsLocalRing.ResidueField O) (hres : res.comp (algebraMap O R) = IsLocalRing.residue O)
    (s : Set R) (hs : s ⊆ IsLocalRing.maximalIdeal R)
    (hsep : ∀ χ χ' : R →+* DualNumber (IsLocalRing.ResidueField O),
      ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).toRingHom.comp χ = res ∧ χ.comp (algebraMap O R) = (algebraMap (IsLocalRing.ResidueField O) (DualNumber (IsLocalRing.ResidueField O))).comp (IsLocalRing.residue O)) →
      ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).toRingHom.comp χ' = res ∧ χ'.comp (algebraMap O R) = (algebraMap (IsLocalRing.ResidueField O) (DualNumber (IsLocalRing.ResidueField O))).comp (IsLocalRing.residue O)) →
      (∀ x ∈ s, χ x = χ' x) → χ = χ') :
    IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span s ⊔ (IsLocalRing.maximalIdeal R) ^ 2 := by
  classical
  set k := ResidueField O with hk
  set I : Ideal R := (maximalIdeal O).map (algebraMap O R) ⊔ Ideal.span s ⊔ (maximalIdeal R) ^ 2 with hI
  have hmemI_map : ∀ o ∈ maximalIdeal O, algebraMap O R o ∈ I := fun o ho =>
    Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))
  have hmemI_s : ∀ x ∈ s, x ∈ I := fun x hx => Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span hx))
  have hmemI_sq : ∀ x ∈ maximalIdeal R, ∀ y ∈ maximalIdeal R, x * y ∈ I := fun x hx y hy =>
    Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul hx hy)

  have hmap_le : (maximalIdeal O).map (algebraMap O R) ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [Ideal.mem_comap, mem_maximalIdeal_iff res hres, ← RingHom.comp_apply, hres]
    exact (IsLocalRing.residue_eq_zero_iff o).mpr ho
  have hI_le : I ≤ maximalIdeal R :=
    sup_le (sup_le hmap_le ((Ideal.span_le).mpr hs)) (Ideal.pow_le_self two_ne_zero)
  refine le_antisymm ?_ hI_le

  intro x hx
  by_contra hxI

  let f : k →+* R ⧸ I := Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk I).comp (algebraMap O R))
    (fun o ho => by rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hmemI_map o ho)
  letI : Algebra k (R ⧸ I) := f.toAlgebra
  have hf : ∀ o : O, f (residue O o) = Ideal.Quotient.mk I (algebraMap O R o) := fun o =>
    Ideal.Quotient.lift_mk _ _ _
  have hsmul : ∀ (c : k) (v : R ⧸ I), c • v = f c * v := fun c v => Algebra.smul_def c v

  set xb : R ⧸ I := Ideal.Quotient.mk I x with hxb
  have hxb_ne : xb ∉ Submodule.span k {(1 : R ⧸ I)} := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
    rw [hsmul, mul_one, hf, hxb, Ideal.Quotient.eq] at hc

    have ho : algebraMap O R o ∈ maximalIdeal R := by
      have := Ideal.add_mem _ (hI_le hc) hx
      rwa [sub_add_cancel] at this
    have ho' : o ∈ maximalIdeal O := by
      rw [mem_maximalIdeal_iff res hres, ← RingHom.comp_apply, hres] at ho
      exact (IsLocalRing.residue_eq_zero_iff o).mp ho
    apply hxI
    have := Ideal.sub_mem _ (hmemI_map o ho') hc
    rwa [sub_sub_cancel] at this

  obtain ⟨φ, hφx, hφ1⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxb_ne inferInstance
  have hφone : φ 1 = 0 := by
    have : φ 1 ∈ (Submodule.span k {(1 : R ⧸ I)}).map φ :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rwa [hφ1, Submodule.mem_bot] at this
  have hφf : ∀ o : O, φ (Ideal.Quotient.mk I (algebraMap O R o)) = 0 := fun o => by
    rw [← hf, ← mul_one (f _), ← hsmul, map_smul, hφone, smul_zero]

  let δ : R → k := fun r => φ (Ideal.Quotient.mk I r)
  have hδ_add : ∀ a b, δ (a + b) = δ a + δ b := fun a b => by simp only [δ, map_add]
  have hδ_alg : ∀ o : O, δ (algebraMap O R o) = 0 := hφf
  have hδ_mul : ∀ a b, δ (a * b) = res a * δ b + res b * δ a := by
    intro a b
    obtain ⟨oa, hoa⟩ := IsLocalRing.residue_surjective (res a)
    obtain ⟨ob, hob⟩ := IsLocalRing.residue_surjective (res b)
    have hma : a - algebraMap O R oa ∈ maximalIdeal R := by
      rw [mem_maximalIdeal_iff res hres, map_sub, ← RingHom.comp_apply, hres, hoa, sub_self]
    have hmb : b - algebraMap O R ob ∈ maximalIdeal R := by
      rw [mem_maximalIdeal_iff res hres, map_sub, ← RingHom.comp_apply, hres, hob, sub_self]
    have hsplit : a * b = algebraMap O R oa * b + algebraMap O R ob * (a - algebraMap O R oa) +
        (a - algebraMap O R oa) * (b - algebraMap O R ob) := by ring
    have h3 : δ ((a - algebraMap O R oa) * (b - algebraMap O R ob)) = 0 := by
      simp only [δ]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hmemI_sq _ hma _ hmb), map_zero]
    have h1 : δ (algebraMap O R oa * b) = res a * δ b := by
      simp only [δ]
      rw [map_mul, ← hf, ← hsmul, map_smul, hoa, smul_eq_mul]
    have h2 : δ (algebraMap O R ob * (a - algebraMap O R oa)) = res b * δ a := by
      simp only [δ]
      rw [map_mul, ← hf, ← hsmul, map_smul, hob, smul_eq_mul, map_sub, map_sub, hφf, sub_zero]
    rw [hsplit, hδ_add, hδ_add, h1, h2, h3, add_zero]

  let χ : R →+* DualNumber k := DDTsep.dualHom res δ hδ_add hδ_mul
  let χ₀ : R →+* DualNumber k := DDTsep.dualHom res (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp)
  have halg : ∀ c : k, algebraMap k (DualNumber k) c = inl c := fun c =>
    TrivSqZeroExt.algebraMap_eq_inl' (S := k) (R := k) (M := k) c
  have hcompat : ∀ (d : R → k) (hda : ∀ a b, d (a + b) = d a + d b)
      (hdm : ∀ a b, d (a * b) = res a * d b + res b * d a), (∀ o : O, d (algebraMap O R o) = 0) →
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (DDTsep.dualHom res d hda hdm) = res ∧
        (DDTsep.dualHom res d hda hdm).comp (algebraMap O R) =
          (algebraMap k (DualNumber k)).comp (IsLocalRing.residue O)) := by
    intro d hda hdm hd0
    refine ⟨?_, ?_⟩
    · ext r
      exact DDTsep.fst_dualHom res d hda hdm r
    · ext o
      · rw [RingHom.comp_apply, DDTsep.fst_dualHom, RingHom.comp_apply, halg, fst_inl, ← RingHom.comp_apply, hres]
      · rw [RingHom.comp_apply, DDTsep.snd_dualHom, hd0, RingHom.comp_apply, halg, snd_inl]
  have hχc := hcompat δ hδ_add hδ_mul hδ_alg
  have hχ₀c := hcompat (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have heq : χ = χ₀ := hsep χ χ₀ hχc hχ₀c (fun y hy => by
    have hy0 : δ y = 0 := by
      simp only [δ]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hmemI_s y hy), map_zero]
    apply TrivSqZeroExt.ext
    · rw [DDTsep.fst_dualHom, DDTsep.fst_dualHom]
    · rw [DDTsep.snd_dualHom, DDTsep.snd_dualHom, hy0])
  apply hφx
  have h := congrArg (fun ψ : R →+* DualNumber k => TrivSqZeroExt.snd (ψ x)) heq
  simp only [χ, χ₀, DDTsep.snd_dualHom] at h
  exact h

#print axioms solution

end S_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn
end P2MW
export P2MW.S_IsLocalRing_maximalIdeal_eq_map_sup_span_sup_sq_of_forall_ringHom_dualNumber_eqOn (solution)
