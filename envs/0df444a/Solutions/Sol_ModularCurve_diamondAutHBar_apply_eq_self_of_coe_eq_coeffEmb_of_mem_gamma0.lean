-- Prove2me | solution 1 for ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/032006c3-07a6-519f-9d17-17f78dbd2e4a

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve
open scoped MatrixGroups ModularForm

namespace DiaMulBody

def toRingAutHom {G : Type*} [Group G] {F : Type*} [Field F] {_inst : Algebra ℚ F} (ρ : G →* (F ≃ₐ[ℚ] F)) :
    G →* RingAut F :=
  MonoidHom.mk' (fun g => (ρ g).toRingEquiv) (fun a b => by show (ρ (a * b)).toRingEquiv = _; rw [map_mul]; rfl)

theorem toRingAutHom_apply {G : Type*} [Group G] {F : Type*} [Field F] {_inst : Algebra ℚ F}
    (ρ : G →* (F ≃ₐ[ℚ] F)) (g : G) (x : F) : toRingAutHom ρ g x = ρ g x := rfl

theorem toRingAutHom_eq_one {G : Type*} [Group G] {F : Type*} [Field F] {_inst : Algebra ℚ F}
    (ρ : G →* (F ≃ₐ[ℚ] F)) (g : G) (h : ρ g = 1) : toRingAutHom ρ g = 1 := by
  show (ρ g).toRingEquiv = 1
  rw [h]
  rfl

theorem exists_gamma0_apply_eq {M : ℕ} [NeZero M] (d : (ZMod M)ˣ) :
    ∃ γ : CongruenceSubgroup.Gamma0 M, (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  set a : ℤ := ((d : ZMod M).val : ℤ) with ha
  have hcop : Nat.Coprime (d : ZMod M).val M := ZMod.val_coe_unit_coprime d
  have hg : Int.gcd a (M : ℤ) = 1 := by rw [ha, Int.gcd_natCast_natCast]; exact hcop
  have hbez : a * Int.gcdA a M + (M : ℤ) * Int.gcdB a M = 1 := by
    have h := Int.gcd_eq_gcd_ab a M
    rw [hg] at h
    push_cast at h
    linarith
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![a, -Int.gcdB a M; (M : ℤ), Int.gcdA a M]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨⟨⟨A, hdet⟩, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((M : ℤ) : ℤ) : ZMod M) = 0
    simp
  · show ((a : ℤ) : ZMod M) = d
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem algHom_ext_laurentBaseChange (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (φ ψ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (h : ∀ x : ↥F₀, φ ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ =
      ψ ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩) :
    φ = ψ := by
  classical
  let Q : IntermediateField (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
    { (AlgHom.equalizer φ ψ) with
      inv_mem' := fun x (hx : φ x = ψ x) => show φ x⁻¹ = ψ x⁻¹ by rw [map_inv₀, map_inv₀, hx] }
  have hval : ∀ x, x ∈ Q ↔ φ x = ψ x := fun x => Iff.rfl
  let S : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
    {z | ∃ x : ↥F₀, (z : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ)}
  have hS : S ⊆ (Q : Set _) := by
    rintro z ⟨x, hx⟩
    have : z = ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ :=
      Subtype.ext hx
    rw [this]
    exact (hval _).mpr (h x)
  have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) S ≤ Q := IntermediateField.adjoin_le_iff.mpr hS
  have htop : IntermediateField.adjoin (AlgebraicClosure ℚ) S = ⊤ := by
    apply le_antisymm le_top
    intro z _
    have hz : (z : LaurentSeries (AlgebraicClosure ℚ)) ∈
        IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (F₀ : Set (LaurentSeries ℚ))) := z.2
    have hle : IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (F₀ : Set (LaurentSeries ℚ))) ≤
        (IntermediateField.adjoin (AlgebraicClosure ℚ) S).map (laurentBaseChange (AlgebraicClosure ℚ) F₀).val := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩,
        IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    obtain ⟨z', hz', hzz'⟩ := hle hz
    have : z' = z := Subtype.ext hzz'
    rw [← this]; exact hz'
  have hQ : (⊤ : IntermediateField (AlgebraicClosure ℚ) _) ≤ Q := htop ▸ hadj
  apply AlgHom.ext
  intro z
  exact (hval z).mp (hQ IntermediateField.mem_top)

section Level

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

noncomputable def emb (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) : ↥(xHFunctionFieldBar N H) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩

theorem exists_rho :
    ∃ ρ : CongruenceSubgroup.Gamma0 N →* RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)),
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))),
        (x : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N) → ρ γ x = x) ∧
      (∀ (d : (ZMod N)ˣ) (γ : CongruenceSubgroup.Gamma0 N), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = (d : ZMod N) →
        ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)), diamondAutHBar N H d (emb N H x) = emb N H (ρ γ x)) := by
  obtain ⟨ρa, hρa_H, -, hρa_0, hρa_slash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ N H
  refine ⟨toRingAutHom ρa, fun γ x hx => ?_, fun d γ hγ x => ?_⟩
  · rw [toRingAutHom_apply]; exact hρa_0 γ x hx
  · have hρ_H : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH N H → toRingAutHom ρa γ = 1 :=
      fun γ hγ => toRingAutHom_eq_one ρa γ (hρa_H γ hγ)
    exact Subtype.ext (ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply N H (toRingAutHom ρa) hρ_H
      (fun γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0 =>
        hρa_slash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hf₁' hg₁' hg0 hg₁0) d γ hγ x)

theorem fix (c : (ZMod N)ˣ) (x : ↥(xHFunctionFieldBar N H)) (y : LaurentSeries ℚ)
    (hy : y ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y) :
    diamondAutHBar N H c x = x := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_rho N H
  obtain ⟨γ, hγ⟩ := exists_gamma0_apply_eq (M := N) c
  have hyH : y ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH N H) :=
    qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H) hy
  have hxe : x = emb N H ⟨y, hyH⟩ := Subtype.ext hx
  rw [hxe, hρ c γ hγ, hρ0 γ _ hy]

private theorem _root_.DiaMulBody.mul_apply (a b : (ZMod N)ˣ) (u : ↥(xHFunctionFieldBar N H)) :
    diamondAutHBar N H a (diamondAutHBar N H b u) = diamondAutHBar N H (a * b) u := by
  obtain ⟨ρ, -, hρ⟩ := exists_rho N H
  obtain ⟨γa, hγa⟩ := exists_gamma0_apply_eq (M := N) a
  obtain ⟨γb, hγb⟩ := exists_gamma0_apply_eq (M := N) b

  have hγab : ((((γa * γb : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = ((a * b : (ZMod N)ˣ) : ZMod N) := by
    have h10 : (((γb : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp γb.2
    have e : (((γa * γb : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) 0 0 : ℤ) =
        ((γa : SL(2, ℤ)) 0 0) * ((γb : SL(2, ℤ)) 0 0) + ((γa : SL(2, ℤ)) 0 1) * ((γb : SL(2, ℤ)) 1 0) := by
      show ((γa : SL(2, ℤ)) * (γb : SL(2, ℤ))).1 0 0 = _
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    push_cast
    rw [h10, mul_zero, add_zero, hγa, hγb]
  have key : (diamondAutHBar N H a).toAlgHom.comp (diamondAutHBar N H b).toAlgHom = (diamondAutHBar N H (a * b)).toAlgHom := by
    refine algHom_ext_laurentBaseChange _ _ _ (fun x => ?_)
    show diamondAutHBar N H a (diamondAutHBar N H b (emb N H x)) = diamondAutHBar N H (a * b) (emb N H x)
    rw [hρ b γb hγb, hρ a γa hγa, hρ (a * b) (γa * γb) hγab, map_mul]
    rfl
  exact congrArg (fun φ : ↥(xHFunctionFieldBar N H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar N H) => φ u) key

p2m_export "DiaMulBody" "mul_apply"

theorem one_apply (u : ↥(xHFunctionFieldBar N H)) : diamondAutHBar N H 1 u = u := by
  obtain ⟨ρ, -, hρ⟩ := exists_rho N H
  have key : (diamondAutHBar N H 1).toAlgHom = AlgHom.id (AlgebraicClosure ℚ) _ := by
    refine algHom_ext_laurentBaseChange _ _ _ (fun x => ?_)
    show diamondAutHBar N H 1 (emb N H x) = emb N H x
    rw [hρ 1 1 (by simp) x, map_one]
    rfl
  exact congrArg (fun φ : ↥(xHFunctionFieldBar N H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar N H) => φ u) key

end Level

end DiaMulBody

theorem solution (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ)
    (x : ↥(xHFunctionFieldBar N H)) (y : LaurentSeries ℚ)
    (hy : y ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y) :
    diamondAutHBar N H c x = x :=
  DiaMulBody.fix N H c x y hy hx

#print axioms solution

end S_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
end P2MW
export P2MW.S_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (solution)
