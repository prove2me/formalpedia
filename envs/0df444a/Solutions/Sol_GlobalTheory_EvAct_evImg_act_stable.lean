-- Prove2me | solution 1 for GlobalTheory.EvAct.evImg_act_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:43.241395+00:00
-- url     : https://prove2.me/submissions/ec964e05-64fc-47d8-80a8-ba1cb904d3da

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvActStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValNatCastSmul
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
namespace GlobalTheory.EvAct
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
private lemma val_natCast_smul {M : Type} [AddCommGroup M] (x : M) (hx : p • x = 0) (n : ℕ) :
    ((n : ZMod p)).val • x = n • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n p, add_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]
private lemma val_sum_mul_smul {M ι : Type} [AddCommGroup M] [Fintype ι] (x : M) (hx : p • x = 0)
    (u v : ι → ZMod p) : (∑ j, u j * v j).val • x = ∑ j, (v j).val • (u j).val • x := by
  have h : (∑ j, u j * v j) = ((∑ j, (v j).val * (u j).val : ℕ) : ZMod p) := by
    push_cast
    simp [mul_comm]
  rw [h, val_natCast_smul x hx, Finset.sum_smul]
  simp only [mul_smul]
private lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO _) = LHom.id Tw.O ∧ B.map (D.ptMap t) (D.fin.y _) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
private lemma tau_p (D : Dat p g B Tw Dt Oe σ cp) (j : Ix g) : p • D.L.τ j 0 = 0 := by
  have h := D.L.τ_tors j 0
  rwa [zero_add, pow_one] at h
private lemma act_ptOf (D : Dat p g B Tw Dt Oe σ cp) (a : Oe) (t : Nb p g) :
    (D.A.act a Tw.O (LHom.id Tw.O) ⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : B.G Tw.O) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have h : (⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : torP B p Tw.O) =
      ∑ j, (t j).val • (⟨D.L.τ j 0, (mem_torP B p _).2 (tau_p D j)⟩ : torP B p Tw.O) := by
    apply Subtype.ext
    simp [ptOf]
  rw [h, map_sum, AddSubgroup.val_finset_sum]
  simp only [map_nsmul, AddSubgroup.coe_nsmul]
  simp only [D.L.ρ_spec, Finset.smul_sum]
  rw [Finset.sum_comm, ptOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec, dotProduct, val_sum_mul_smul _ (tau_p D k)]
  rfl
private lemma red_mulVec (M : Matrix (Ix g) (Ix g) ℤ_[p]) (t : TT p g) :
    red p g (M *ᵥ t) = (M.map PadicInt.toZMod) *ᵥ red p g t := by
  funext k
  exact (RingHom.map_mulVec PadicInt.toZMod M t k)
private lemma eval_congr (D : Dat p g B Tw Dt Oe σ cp) (F : ∀ i, (D.fin.AAx i : Type))
    {i j : D.fin.ι} (φ : LHom (D.fin.AAx i) Tw.O) (φ' : LHom (D.fin.AAx j) Tw.O) (h : i = j)
    (h' : HEq φ φ') : φ.1 (F i) = φ'.1 (F j) := by
  subst h
  rw [eq_of_heq h']
private lemma evAll_act (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C]
    [Algebra (Tw.O : Type) C] (a : Oe) (F : ∀ i, (D.fin.AAx i : Type)) :
    ∃ F' : ∀ i, (D.fin.AAx i : Type), ∀ t : Nb p g,
      D.evAll C F' t = D.evAll C F (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have key := fun i => D.fin.univ (D.fin.AAx i) (D.fin.sO i)
    (D.A.act a (D.fin.AAx i) (D.fin.sO i) ⟨D.fin.y i, (mem_torP B p _).2 (D.fin.y_p i)⟩ : B.G _)
    ((mem_torP B p _).1 (Subtype.property _))
  choose m α hs hy _ using key
  refine ⟨fun i => (α i).1 (F (m i)), fun t => ?_⟩
  obtain ⟨h1, h2, -⟩ := ptMap_spec D t
  obtain ⟨-, -, h3⟩ := ptMap_spec D (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t)
  have e1 : ((D.ptMap t).comp (α (D.ptIdx t))).comp (D.fin.sO _) = LHom.id Tw.O := by
    rw [← h1, ← hs (D.ptIdx t)]
    rfl
  have e2 : B.map ((D.ptMap t).comp (α (D.ptIdx t))) (D.fin.y _) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
    rw [B.map_comp, hy, D.A.act_nat a _ _ _ h1, ← act_ptOf]
    congr 2
    exact Subtype.ext h2
  obtain ⟨h4, h5⟩ := h3 _ _ e1 e2
  unfold Dat.evAll
  rw [← eval_congr D F _ _ h4 h5]
  rfl
end GlobalTheory.EvAct
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.EvAct
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
namespace GlobalTheory.EvAct
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvActStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ a f hf
  refine ⟨fun t => f (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t), ?_, fun t => by rw [red_mulVec]⟩
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, rfl⟩ := hx
    obtain ⟨F', hF'⟩ := evAll_act D C a F
    exact Submodule.subset_span ⟨F', funext hF'⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx
end GlobalTheory.EvAct
