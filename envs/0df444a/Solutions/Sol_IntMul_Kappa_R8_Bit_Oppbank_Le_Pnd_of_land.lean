-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Le_Pnd_of_land
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:00:22.560004+00:00
-- url     : https://prove2.me/submissions/81f535d4-584d-42c9-998b-1faed8507ed9

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2

private theorem mat_ext {P Q : M23} (h : ∀ u, P *ᵥ u = Q *ᵥ u) : P = Q := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun u => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]

private theorem decomp {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V)) (u : V23) :
    ∃ a ∈ V, ∃ b ∈ Bf.orthogonal V, u = a + b := by
  have : u ∈ V ⊔ Bf.orthogonal V := by rw [h.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 this
  exact ⟨a, ha, b, hb, e.symm⟩

private theorem IsPrj.eq {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P Q : M23} (hP : IsPrj P V) (hQ : IsPrj Q V) : P = Q := by
  apply mat_ext
  intro u
  obtain ⟨a, ha, b, hb, rfl⟩ := decomp h u
  rw [mulVec_add, mulVec_add, hP.1 a ha, hQ.1 a ha, hP.2 b hb, hQ.2 b hb]

private theorem IsPrj.mem {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P : M23} (hP : IsPrj P V) (u : V23) :
    P *ᵥ u ∈ V ∧ u - P *ᵥ u ∈ Bf.orthogonal V := by
  obtain ⟨a, ha, b, hb, rfl⟩ := decomp h u
  rw [mulVec_add, hP.1 a ha, hP.2 b hb, add_zero, add_sub_cancel_left]
  exact ⟨ha, hb⟩

private theorem IsPrj.nested {V V' : Submodule ℚ V23} (hVV : V ≤ V')
    (h : IsCompl V (Bf.orthogonal V)) (h' : IsCompl V' (Bf.orthogonal V'))
    {P P' : M23} (hP : IsPrj P V) (hP' : IsPrj P' V') :
    P' * P = P ∧ P * P' = P := by
  have horth : Bf.orthogonal V' ≤ Bf.orthogonal V := LinearMap.BilinForm.orthogonal_le hVV
  constructor
  · exact IsPrj.eq h ⟨fun v hv => by rw [← mulVec_mulVec, hP.1 v hv, hP'.1 v (hVV hv)],
      fun w hw => by rw [← mulVec_mulVec, hP.2 w hw, mulVec_zero]⟩ hP
  · refine IsPrj.eq h ⟨fun v hv => by rw [← mulVec_mulVec, hP'.1 v (hVV hv), hP.1 v hv],
      fun w hw => ?_⟩ hP
    rw [← mulVec_mulVec]
    have hm := (IsPrj.mem h' hP' w).2
    have : P' *ᵥ w = w - (w - P' *ᵥ w) := by abel
    rw [this, mulVec_sub, hP.2 w hw, hP.2 _ (horth hm), sub_zero]

private theorem prjM_spec (V : Submodule ℚ V23) (h : IsCompl V (Bf.orthogonal V)) :
    IsPrj (prjM V h) V := by
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · rw [prjM, LinearMap.toMatrix'_mulVec, Submodule.projection_apply_of_mem_left h hv]
  · rw [prjM, LinearMap.toMatrix'_mulVec, Submodule.projection_apply_of_mem_right h hw]

private theorem Pnd_prj {sup : ℕ} (h : HasCentre sup) : IsPrj (Pnd sup) (spanS sup) := by
  rw [Pnd_eq_prj h]; exact prjM_spec _ _

private theorem spanS_mono {a b : ℕ}
    (h : ∀ i, a.testBit i = true → b.testBit i = true) : spanS a ≤ spanS b := by
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, h i hi, rfl⟩

private theorem land_testBit {sa sb : ℕ} (h : Nat.land sa sb = sa) {i : ℕ}
    (hi : sa.testBit i = true) : sb.testBit i = true := by
  have : (sa &&& sb).testBit i = true := by
    change (Nat.land sa sb).testBit i = true
    rw [h]; exact hi
  rw [Nat.testBit_land, Bool.and_eq_true] at this
  exact this.2

theorem solution {sa sb : ℕ}
    (hCsa : HasCentre sa) (hCsb : HasCentre sb)
    (h : Nat.land sa sb = sa) :
    Le (Pnd sa) (Pnd sb) := by
  have hspan : spanS sa ≤ spanS sb :=
    spanS_mono fun i hi => land_testBit h hi
  exact IsPrj.nested hspan (compl_spanS hCsa) (compl_spanS hCsb)
    (Pnd_prj hCsa) (Pnd_prj hCsb)
