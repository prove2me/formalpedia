-- Prove2me | solution 1 for ModularForm.exists_gamma0_weight_two_forall_tendsto_slash_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/77fdf636-448c-5697-870d-b87d46702c17

import Mathlib
import Theorems.Thm_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty

set_option autoImplicit false

open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix
p2m_open "UpperHalfPlane~I"
open Filter

noncomputable section

namespace EIS2W0

variable {N : ℕ} [NeZero N] {k : ℤ}

local notation "Γ₀" => CongruenceSubgroup.Gamma0

abbrev red (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))

omit [NeZero N] in
lemma red_apply (g : SL(2, ℤ)) (i j : Fin 2) : (red N g) i j = ((g i j : ℤ) : ZMod N) := rfl

def borel (N : ℕ) : Subgroup SL(2, ZMod N) where
  carrier := {β | β 1 0 = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [ha]

omit [NeZero N] in
lemma mem_borel {β : SL(2, ZMod N)} : β ∈ borel N ↔ β 1 0 = 0 := Iff.rfl

scoped instance : Fintype (borel N) := Fintype.ofFinite _

omit [NeZero N] in
lemma red_mem_borel {γ : SL(2, ℤ)} (hγ : γ ∈ Γ₀ N) : red N γ ∈ borel N := by
  rw [mem_borel, red_apply]
  exact (CongruenceSubgroup.Gamma0_mem.mp hγ)

lemma exists_lift (β : SL(2, ZMod N)) (hβ : β 1 0 = 0) :
    ∃ γ : SL(2, ℤ), γ ∈ Γ₀ N ∧ red N γ = β := by
  have hdet : (β 0 0) * (β 1 1) = 1 := by
    have := β.prop
    rw [Matrix.det_fin_two, hβ, mul_zero, sub_zero] at this
    exact this
  set p : ℤ := ((β 0 0).val : ℤ) with hp
  set s : ℤ := ((β 1 1).val : ℤ) with hs
  have hp' : ((p : ZMod N)) = β 0 0 := by simp [hp]
  have hs' : ((s : ZMod N)) = β 1 1 := by simp [hs]
  obtain ⟨u, hu⟩ : ∃ u : ℤ, p * s - 1 = N * u := by
    have : ((p * s - 1 : ℤ) : ZMod N) = 0 := by
      push_cast; rw [hp', hs', hdet, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  let M₀ : SL(2, ℤ) := ⟨!![p, u; N, s], by rw [Matrix.det_fin_two_of]; linarith⟩
  have hM₀ : M₀ ∈ Γ₀ N := by simp [CongruenceSubgroup.Gamma0_mem, M₀]
  set j : ℤ := (((β 1 1) * (β 0 1 - (u : ZMod N))).val : ℤ) with hj
  have hj' : ((j : ZMod N)) = (β 1 1) * (β 0 1 - (u : ZMod N)) := by simp [hj]
  refine ⟨M₀ * ModularGroup.T ^ j, Subgroup.mul_mem _ hM₀ (Subgroup.zpow_mem _ ?_ _), ?_⟩
  · simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]
  · apply Matrix.SpecialLinearGroup.ext
    intro i a
    rw [red_apply]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, M₀]
    fin_cases i <;> fin_cases a
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hp']
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', mul_one]
      push_cast
      rw [hp', hj', ← mul_assoc, hdet, one_mul, sub_add_cancel]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hβ]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hs']

def lift (β : SL(2, ZMod N)) : SL(2, ℤ) :=
  if h : β 1 0 = 0 then (exists_lift β h).choose else 1

lemma lift_mem (β : borel N) : lift β.1 ∈ Γ₀ N := by
  have hβ : β.1 1 0 = 0 := mem_borel.mp β.2
  rw [lift, dif_pos hβ]; exact (exists_lift β.1 hβ).choose_spec.1

lemma red_lift (β : borel N) : red N (lift β.1) = β.1 := by
  have hβ : β.1 1 0 = 0 := mem_borel.mp β.2
  rw [lift, dif_pos hβ]; exact (exists_lift β.1 hβ).choose_spec.2

def Av (k : ℤ) (h : ℍ → ℂ) : ℍ → ℂ := ∑ β : borel N, h ∣[k] lift β.1

omit [NeZero N] in
lemma slash_mul_of_invariant {h : ℍ → ℂ} (hinv : ∀ e ∈ Γ(N), h ∣[k] e = h) (g : SL(2, ℤ))
    {e : SL(2, ℤ)} (he : e ∈ Γ(N)) : h ∣[k] (g * e) = h ∣[k] g := by
  have hconj : g * e * g⁻¹ ∈ Γ(N) := (CongruenceSubgroup.Gamma_normal N).conj_mem e he g
  calc h ∣[k] (g * e) = h ∣[k] ((g * e * g⁻¹) * g) := by group
    _ = (h ∣[k] (g * e * g⁻¹)) ∣[k] g := by rw [SlashAction.slash_mul]
    _ = h ∣[k] g := by rw [hinv _ hconj]

lemma Av_slash {h : ℍ → ℂ} (hinv : ∀ e ∈ Γ(N), h ∣[k] e = h) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ₀ N) :
    Av (N := N) k h ∣[k] γ = Av (N := N) k h := by
  simp only [Av, SlashAction.sum_slash, ← SlashAction.slash_mul]
  set δ : borel N := ⟨red N γ, red_mem_borel hγ⟩ with hδ
  rw [← Equiv.sum_comp (Equiv.mulRight δ) (fun β : borel N => h ∣[k] lift β.1)]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [Equiv.coe_mulRight]
  have hmem : (lift β.1 * γ)⁻¹ * lift (β * δ).1 ∈ Γ(N) := by
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, map_mul, red_lift, red_lift]
    simp [hδ]
  have : lift (β * δ).1 = (lift β.1 * γ) * ((lift β.1 * γ)⁻¹ * lift (β * δ).1) := by group
  rw [this, slash_mul_of_invariant hinv _ hmem]

omit [NeZero N] in
lemma invariant_of_slashInvariantForm (F : SlashInvariantForm Γ(N) k) :
    ∀ e ∈ Γ(N), ⇑F ∣[k] e = ⇑F := by
  intro e he
  have := SlashInvariantForm.slash_action_eqn F (Matrix.SpecialLinearGroup.mapGL ℝ e) ⟨e, he, rfl⟩
  simpa [ModularForm.SL_slash, Matrix.SpecialLinearGroup.mapGL] using this

omit [NeZero N] in
lemma mdifferentiable_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (hF : ∀ i ∈ s, MDiff (F i)) : MDiff (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (c := (0 : ℂ)))
  | insert i s hi IH =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add (IH fun j hj => hF j (Finset.mem_insert_of_mem hj))

omit [NeZero N] in
lemma isBoundedAtImInfty_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsBoundedAtImInfty (F i)) : IsBoundedAtImInfty (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperHalfPlane.zero_form_isBoundedAtImInfty
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def avMF (F : ModularForm Γ(N) k) : ModularForm (Γ₀ N) k where
  toFun := Av (N := N) k ⇑F
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := Av_slash (N := N) (k := k) (invariant_of_slashInvariantForm F.toSlashInvariantForm) hγ
    simp [ModularForm.SL_slash, Matrix.SpecialLinearGroup.mapGL] at this
    exact this
  holo' := by
    show MDiff (Av (N := N) k ⇑F)
    unfold Av
    refine mdifferentiable_finset_sum _ _ fun β _ => ?_
    rw [ModularForm.SL_slash]
    exact F.holo'.slash k _
  bdd_at_cusps' {c} hc := by
    show c.IsBoundedAt (Av (N := N) k ⇑F) k
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro σ _
    simp only [Av, SlashAction.sum_slash, ← SlashAction.slash_mul]
    exact isBoundedAtImInfty_finset_sum _ _ fun β _ => ModularFormClass.bdd_at_infty_slash F _

lemma coe_avMF (F : ModularForm Γ(N) k) : ⇑(avMF F) = Av (N := N) k ⇑F := rfl

lemma tendsto_avMF_slash (F : ModularForm Γ(N) k) (w : SL(2, ℤ) → ℂ)
    (hw : ∀ σ : SL(2, ℤ), Tendsto (fun τ => ((⇑F) ∣[k] σ) τ) atImInfty (𝓝 (w σ))) (σ : SL(2, ℤ)) :
    Tendsto (fun τ => ((⇑(avMF F)) ∣[k] σ) τ) atImInfty (𝓝 (∑ β : borel N, w (lift β.1 * σ))) := by
  rw [coe_avMF]
  simp only [Av, SlashAction.sum_slash, ← SlashAction.slash_mul]
  have : (fun τ => (∑ β : borel N, (⇑F) ∣[k] (lift β.1 * σ)) τ)
      = fun τ => ∑ β : borel N, ((⇑F) ∣[k] (lift β.1 * σ)) τ := by
    funext τ; simp [Finset.sum_apply]
  rw [this]
  exact tendsto_finsetSum _ fun β _ => hw _

omit [NeZero N] in
lemma Gamma_le_Gamma0 : Γ(N) ≤ Γ₀ N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  exact CongruenceSubgroup.Gamma0_mem.mpr hγ.2.2.1

omit [NeZero N] in

lemma apply_out_inv_eq (v : SL(2, ℤ) → ℂ) (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ₀ N → v (γ * σ) = v σ)
    (x : SL(2, ℤ)) :
    v (QuotientGroup.mk x : SL(2, ℤ) ⧸ Γ(N)).out⁻¹ = v (QuotientGroup.mk x : SL(2, ℤ) ⧸ Γ₀ N).out⁻¹ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul (Γ(N)) x
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_out_eq_mul (Γ₀ N) x
  rw [hg, hg', mul_inv_rev, mul_inv_rev, hv _ _ (Subgroup.inv_mem _ (Gamma_le_Gamma0 g.2)),
    hv _ _ (Subgroup.inv_mem _ g'.2)]

lemma finsum_gamma_eq (v : SL(2, ℤ) → ℂ) (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ₀ N → v (γ * σ) = v σ) :
    ∑ᶠ q : SL(2, ℤ) ⧸ Γ(N), v q.out⁻¹ =
      (Nat.card (Γ₀ N ⧸ (Γ(N)).subgroupOf (Γ₀ N)) : ℂ) * ∑ᶠ q : SL(2, ℤ) ⧸ Γ₀ N, v q.out⁻¹ := by
  classical
  letI : Fintype (SL(2, ℤ) ⧸ Γ(N)) := (Γ(N)).fintypeQuotientOfFiniteIndex
  letI : Fintype (SL(2, ℤ) ⧸ Γ₀ N) := (Γ₀ N).fintypeQuotientOfFiniteIndex
  letI : Fintype (Γ₀ N ⧸ (Γ(N)).subgroupOf (Γ₀ N)) := ((Γ(N)).subgroupOf (Γ₀ N)).fintypeQuotientOfFiniteIndex
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]

  set V₀ : SL(2, ℤ) ⧸ Γ₀ N → ℂ := fun p => v p.out⁻¹ with hV₀
  set π : SL(2, ℤ) ⧸ Γ(N) → SL(2, ℤ) ⧸ Γ₀ N :=
    fun q => Quotient.map' id (fun _ _ h => QuotientGroup.leftRel_apply.mpr
      (Gamma_le_Gamma0 (QuotientGroup.leftRel_apply.mp h))) q with hπ
  have hval : ∀ q : SL(2, ℤ) ⧸ Γ(N), v q.out⁻¹ = V₀ (π q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact apply_out_inv_eq v hv x
  simp_rw [hval]

  set e := Subgroup.quotientEquivProdOfLE (Gamma_le_Gamma0 (N := N)) with he
  have hfst : ∀ q : SL(2, ℤ) ⧸ Γ(N), (e q).1 = π q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  rw [← Equiv.sum_comp e.symm (fun q => V₀ (π q))]
  have : ∀ pr : (SL(2, ℤ) ⧸ Γ₀ N) × (Γ₀ N ⧸ (Γ(N)).subgroupOf (Γ₀ N)), V₀ (π (e.symm pr)) = V₀ pr.1 := by
    intro pr
    rw [← hfst, Equiv.apply_symm_apply]
  simp_rw [this]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

theorem main (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ₀ N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ Γ₀ N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (Γ₀ N) 2, ∀ σ : SL(2, ℤ),
      Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) atImInfty (𝓝 (v σ)) := by
  classical
  have hv0 : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ₀ N → v (γ * σ) = v σ := fun σ γ hγ => by
    simpa using hv σ γ hγ 0

  set M : ℕ := Fintype.card (borel N) with hM
  have hMpos : (M : ℂ) ≠ 0 := by
    have : 0 < M := Fintype.card_pos
    exact_mod_cast this.ne'
  set w : SL(2, ℤ) → ℂ := fun σ => (M : ℂ)⁻¹ * v σ with hw
  have hw1 : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ(N) → ∀ j : ℤ, w (γ * σ * ModularGroup.T ^ j) = w σ := by
    intro σ γ hγ j
    simp only [hw, hv σ γ (Gamma_le_Gamma0 hγ) j]
  have hw2 : ∀ σ : SL(2, ℤ), w (-σ) = w σ := by
    intro σ
    have h1 : (-1 : SL(2, ℤ)) ∈ Γ₀ N := by rw [CongruenceSubgroup.Gamma0_mem]; simp
    have := hv σ (-1) h1 0
    simp only [zpow_zero, mul_one, neg_mul, one_mul] at this
    simp only [hw, this]
  have hw3 : ∑ᶠ q : SL(2, ℤ) ⧸ Γ(N), w q.out⁻¹ = 0 := by
    have h1 : ∑ᶠ q : SL(2, ℤ) ⧸ Γ(N), w q.out⁻¹ = (M : ℂ)⁻¹ * ∑ᶠ q : SL(2, ℤ) ⧸ Γ(N), v q.out⁻¹ := by
      simp only [hw]
      exact (mul_finsum _ _).symm
    rw [h1, finsum_gamma_eq v hv0, hsum, mul_zero, mul_zero]
  obtain ⟨F, hF⟩ := ModularForm.exists_gamma_weight_two_forall_tendsto_slash_atImInfty N w hw1 hw2 hw3
  refine ⟨avMF F, fun σ => ?_⟩
  have h := tendsto_avMF_slash F w hF σ
  have hval : (∑ β : borel N, w (lift β.1 * σ)) = v σ := by
    have : ∀ β : borel N, w (lift β.1 * σ) = (M : ℂ)⁻¹ * v σ := fun β => by
      simp only [hw, hv0 σ _ (lift_mem β)]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hM]
    field_simp
  rw [hval] at h
  exact h

end EIS2W0
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty.EIS2W0"

end
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty.EIS2W0"

theorem solution (N : ℕ) [NeZero N] (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) 2, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) :=
  EIS2W0.main v hv hsum

end S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty
end P2MW
export P2MW.S_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty (solution)
