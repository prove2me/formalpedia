-- Prove2me | solution 1 for IsZpExtension.finite_layers
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:40:53.871047+00:00
-- url     : https://prove2.me/submissions/fcf2fd55-b91b-4119-8da5-049d43da7be1

import Definitions.Def_ZpExtension
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace ZPEXTAux

variable {p : ℕ} [hp : Fact p.Prime]

/-- The subgroup `p^n ℤ_p` of `Multiplicative ℤ_[p]`. -/
noncomputable def powSub (p : ℕ) [Fact p.Prime] (n : ℕ) : Subgroup (Multiplicative ℤ_[p]) :=
  (PadicInt.toZModPow (p := p) n).toAddMonoidHom.toMultiplicative.ker

lemma mem_powSub (n : ℕ) (x : Multiplicative ℤ_[p]) :
    x ∈ powSub p n ↔ x.toAdd ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  rw [← PadicInt.ker_toZModPow]
  rfl

lemma index_powSub (n : ℕ) : (powSub p n).index = p ^ n := by
  rw [powSub, Subgroup.index_ker]
  have hs : Function.Surjective
      (PadicInt.toZModPow (p := p) n).toAddMonoidHom.toMultiplicative := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n) y.toAdd
    exact ⟨Multiplicative.ofAdd x, hx⟩
  rw [MonoidHom.range_eq_top.mpr hs, Subgroup.card_top]
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]

lemma isOpen_powSub (n : ℕ) : IsOpen ((powSub p n : Set (Multiplicative ℤ_[p]))) := by
  have : (powSub p n : Set (Multiplicative ℤ_[p])) =
      Multiplicative.toAdd ⁻¹' {x : ℤ_[p] | ‖x‖ < (p : ℝ) ^ (-(n : ℤ) + 1)} := by
    ext x
    simp only [SetLike.mem_coe, mem_powSub, Set.mem_preimage, Set.mem_ofPred_eq,
      ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
  rw [this]
  exact (isOpen_lt continuous_norm continuous_const).preimage continuous_toAdd

lemma eq_powSub_of_isOpen (S : Subgroup (Multiplicative ℤ_[p]))
    (hS : IsOpen (S : Set (Multiplicative ℤ_[p]))) : ∃ k, S = powSub p k := by
  have h1 : (S : Set _) ∈ nhds (1 : Multiplicative ℤ_[p]) := hS.mem_nhds S.one_mem
  have h2 : Multiplicative.ofAdd ⁻¹' (S : Set _) ∈ nhds (0 : ℤ_[p]) :=
    continuous_ofAdd.continuousAt.preimage_mem_nhds (by simpa using h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h2
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have hsub : ∀ x : ℤ_[p], x ∈ Ideal.span {(p : ℤ_[p]) ^ n} →
      Multiplicative.ofAdd x ∈ S := by
    intro x hx
    refine hball (show x ∈ Metric.ball (0 : ℤ_[p]) ε from ?_)
    rw [Metric.mem_ball, dist_zero_right]
    exact ((PadicInt.norm_le_pow_iff_mem_span_pow x n).mpr hx).trans_lt hn
  let I : Ideal ℤ_[p] :=
    { carrier := {x | Multiplicative.ofAdd x ∈ S}
      add_mem' := fun {a b} ha hb => by
        show Multiplicative.ofAdd (a + b) ∈ S
        rw [ofAdd_add]
        exact S.mul_mem ha hb
      zero_mem' := S.one_mem
      smul_mem' := fun c x hx => by
        have e : c • x = (c.appr n : ℕ) • x + (c - c.appr n) * x := by
          rw [smul_eq_mul, nsmul_eq_mul]; ring
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [e, ofAdd_add, ofAdd_nsmul]
        exact S.mul_mem (S.pow_mem hx _)
          (hsub _ (Ideal.mul_mem_right _ _ (PadicInt.appr_spec n c))) }
  have hI : I ≠ ⊥ := by
    intro h
    have hmem : ((p : ℤ_[p]) ^ n) ∈ I := hsub _ (Ideal.subset_span rfl)
    rw [h, Ideal.mem_bot] at hmem
    exact pow_ne_zero n (by exact_mod_cast hp.out.ne_zero) hmem
  obtain ⟨k, hk⟩ := PadicInt.ideal_eq_span_pow_p hI
  refine ⟨k, ?_⟩
  ext x
  rw [mem_powSub, ← hk]
  rfl

end ZPEXTAux

open ZPEXTAux

theorem solution {p : ℕ} [Fact p.Prime] {K L : Type*} [Field K] [Field L]
    [Algebra K L] (h : IsZpExtension p K L) :
    (∀ n : ℕ, ∃! M : IntermediateField K L, Module.finrank K M = p ^ n) ∧
    ∀ M : IntermediateField K L, FiniteDimensional K M →
      IsGalois K M ∧ IsCyclic Gal(M/K) ∧ ∃ n : ℕ, Module.finrank K M = p ^ n := by
  obtain ⟨hGal, ⟨φ⟩⟩ := h
  let f : Gal(L/K) →* Multiplicative ℤ_[p] := φ.toMulEquiv.toMonoidHom
  have hf : Function.Surjective f := φ.surjective
  have hf_apply : ∀ x, f x = φ x := fun _ => rfl
  -- fixing subgroups of finite layers are preimages of `p^k ℤ_p`
  have key : ∀ M : IntermediateField K L, FiniteDimensional K M →
      ∃ k, M.fixingSubgroup = (powSub p k).comap f := by
    intro M hM
    have hopen : IsOpen (M.fixingSubgroup : Set Gal(L/K)) :=
      IntermediateField.fixingSubgroup_isOpen M
    let S : Subgroup (Multiplicative ℤ_[p]) :=
      M.fixingSubgroup.comap φ.symm.toMulEquiv.toMonoidHom
    have hS : IsOpen (S : Set (Multiplicative ℤ_[p])) := hopen.preimage φ.symm.continuous
    obtain ⟨k, hk⟩ := eq_powSub_of_isOpen S hS
    refine ⟨k, ?_⟩
    rw [← hk]
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    show x ∈ _ ↔ φ.symm (φ x) ∈ _
    rw [φ.symm_apply_apply]
  have hfin : ∀ k, Module.finrank K (IntermediateField.fixedField ((powSub p k).comap f)) = p ^ k
      ∧ (IntermediateField.fixedField ((powSub p k).comap f)).fixingSubgroup
        = (powSub p k).comap f := by
    intro k
    have hcl : IsClosed (((powSub p k).comap f : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
      (Subgroup.isClosed_of_isOpen _ (isOpen_powSub k)).preimage φ.continuous
    have hfix := InfiniteGalois.fixingSubgroup_fixedField (⟨(powSub p k).comap f, hcl⟩ :
      ClosedSubgroup Gal(L/K))
    refine ⟨?_, hfix⟩
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    erw [hfix]
    rw [Subgroup.index_comap_of_surjective _ hf, index_powSub]
  have hfinrank : ∀ M : IntermediateField K L, FiniteDimensional K M →
      ∃ k, M.fixingSubgroup = (powSub p k).comap f ∧ Module.finrank K M = p ^ k := by
    intro M hM
    obtain ⟨k, hk⟩ := key M hM
    refine ⟨k, hk, ?_⟩
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hk,
      Subgroup.index_comap_of_surjective _ hf, index_powSub]
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b =>
    φ.injective (by rw [map_mul, map_mul, mul_comm])
  refine ⟨fun n => ⟨_, (hfin n).1, fun M hM => ?_⟩, fun M hM => ?_⟩
  · have hMfd : FiniteDimensional K M :=
      Module.finite_of_finrank_pos (by rw [hM]; exact pow_pos (Fact.out : p.Prime).pos n)
    obtain ⟨k, hk, hk'⟩ := hfinrank M hMfd
    have hkn : k = n := Nat.pow_right_injective (Fact.out : p.Prime).two_le (hk'.symm.trans hM)
    subst hkn
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, hk]
  · obtain ⟨k, hk, hk'⟩ := hfinrank M hM
    have hnormal : M.fixingSubgroup.Normal :=
      ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
    have hMGal : IsGalois K M := (InfiniteGalois.normal_iff_isGalois M).mp hnormal
    refine ⟨hMGal, ?_, k, hk'⟩
    let g₀ : Gal(L/K) := φ.symm (Multiplicative.ofAdd 1)
    let ψ : Multiplicative ℤ →* Gal(M/K) :=
      (AlgEquiv.restrictNormalHom M).comp (zpowersHom Gal(L/K) g₀)
    refine isCyclic_of_surjective ψ ?_
    intro τ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    let m : ℕ := (Multiplicative.toAdd (φ g)).appr k
    refine ⟨Multiplicative.ofAdd (m : ℤ), ?_⟩
    simp only [ψ, MonoidHom.comp_apply, zpowersHom_apply, toAdd_ofAdd]
    rw [MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hk, Subgroup.mem_comap,
      mem_powSub]
    have hφ : f (g⁻¹ * g₀ ^ (m : ℤ)) =
        Multiplicative.ofAdd (-(Multiplicative.toAdd (φ g)) + (m : ℤ_[p])) := by
      rw [map_mul, map_inv, map_zpow, hf_apply, hf_apply, φ.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      simp
    rw [hφ, toAdd_ofAdd, neg_add_eq_sub, ← neg_sub]
    exact neg_mem (PadicInt.appr_spec k _)
