-- Prove2me | solution 1 for GlobalTheory.evHt_of_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:16.139463+00:00
-- url     : https://prove2.me/submissions/16f3e315-81b0-4154-8b5f-f343b8810a5d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvHtStatement
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_DualLattices_DualPairInh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HtDualExists
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_____9b8197f73975
import Theorems.Thm_ReciprocityTheory_PGsh_ATower_char_R
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_map
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_sum
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_unique
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_zsmul
import Theorems.Thm_ReciprocityTheory_PGsh_pairingProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
private lemma htDualRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    htDualRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [htDualRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl
private lemma htDualRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : htDualRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [htDualRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]
private lemma htDualRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (htDualRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [htDualRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n a _ =>
    have h := htDualRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp
private lemma htDual_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { htDualRing Dq ψ with
      commutes' := fun r => by
        show htDualRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => htDualRing_π Dq ψ x,
    fun x => ?_, htDualRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (htDualRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((htDualRing_π Dq ψ a) ▸ h1)
  · show htDualRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C]
    rfl
private lemma ht_padic_val {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    ∃ b : ℤ_[p], a - ((PadicInt.toZMod a).val : ℤ_[p]) = p * b := by
  have h : a - ((PadicInt.toZMod a).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rw [← hb, mul_comm]⟩
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvHtStatement D) := by
  intro hLam R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  have hg : 0 < g := Nat.zero_lt_of_lt k.2
  obtain ⟨-, -, hL⟩ := hLam D hg
  clear hLam
  choose Λ μ j ρΛ _ hμ _ _ hψ using hL
  have hB1 := pairingProperties B
  have hchar := Tw.toATower.char_R 0
  have hcharΛ : ∀ i, ((p ^ (0 + 1) : ℕ) : (Λ i : Type)) = 0 := fun i => by
    rw [← map_natCast (j i).1, hchar, map_zero]
  have hy : ∀ i, (p ^ (0 + 1)) • B.map (μ i) (D.fin.y i) = 0 := fun i => by
    rw [← map_nsmul, zero_add, pow_one, D.fin.y_p, map_zero]
  choose h hh using fun i =>
    B.isHeight_exists hB1 (DualNum.dualPair (Λ i)) (p ^ (0 + 1)) (hcharΛ i) _ (hy i)
  choose F hF using fun i => hμ i (h i (D.ch.gb k))
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  obtain ⟨hs, hyt, -⟩ := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  change (D.ptMap (red p g t)).comp (D.fin.sO (D.ptIdx (red p g t))) = LHom.id Tw.O at hs
  change B.map (D.ptMap (red p g t)) (D.fin.y (D.ptIdx (red p g t))) = ptOf B D.L.τ (red p g t) at hyt
  obtain ⟨ψ, hψμ, -, -⟩ := hψ _ _ hs
  obtain ⟨f, f1, f2, f3⟩ := htDual_exists (Dt.Dp 0) ψ
  have H1 := B.isHeight_map hB1 _ _ ψ f f1 f2 f3 _ _ _ (hh (D.ptIdx (red p g t)))
  rw [← B.map_comp, hψμ, B.map_comp, hyt] at H1
  choose b hb using fun i => ht_padic_val (t i)
  have hp0 : ((p : ℕ) : (Tw.R 0 : Type)) = 0 := by simpa using hchar
  have hy2 : ∀ i, (p ^ (0 + 1)) • B.map (Tw.q 0) (D.L.τ i 0) = 0 := fun i => by
    rw [← map_nsmul, D.L.τ_tors, map_zero]
  have H2 := B.isHeight_sum hB1 (Dt.Dp 0) _ hchar Finset.univ
    (fun i => (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0))
    (fun i => by rw [smul_comm, hy2, smul_zero]) _
    (fun i => B.isHeight_zsmul hB1 (Dt.Dp 0) _ hchar (hy2 i) (D.L.ht_spec i 0) _)
  have e1 : ∑ i, (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0) =
      B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) := by
    simp only [ptOf, map_sum, map_nsmul, natCast_zsmul]
  rw [e1] at H2
  have hyp : (p ^ (0 + 1)) • B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) = 0 := by
    rw [← map_nsmul, zero_add, pow_one, D.pt_p, map_zero]
  have hU := LinearMap.congr_fun (B.isHeight_unique hB1 _ _ hchar _ hyp _ _ H1 H2) (D.ch.gb k)
  have hmem : (D.H.Ht *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have e2 : (Tw.q 0).1 ((D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t)))) =
        ψ.1 (h (D.ptIdx (red p g t)) (D.ch.gb k)) := by
      rw [← hF]
      exact (congrArg (fun u : LHom _ _ => u.1 (F (D.ptIdx (red p g t)))) hψμ).symm
    rw [e2]
    refine Eq.trans ?_ hU.symm
    rw [LinearMap.sum_apply, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e3 : t i = ((red p g t i).val : ℤ_[p]) + p * b i := by
      rw [← hb i]
      show t i = ((PadicInt.toZMod (t i)).val : ℤ_[p]) + _
      ring
    rw [D.L.Ht_eq, Function.comp_apply, e3]
    rw [map_add, map_mul (algebraMap ℤ_[p] (Tw.O : Type)), map_natCast, map_natCast, map_mul, map_add,
      map_mul (Tw.q 0).1, map_natCast, map_natCast, hp0, zero_mul, add_zero, natCast_zsmul,
      LinearMap.smul_apply, nsmul_eq_mul, mul_comm]
    rfl
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  rw [Dat.evAll, ← map_sub, ← hr, mul_comm]
end GlobalTheory
