-- Prove2me | solution 1 for MvFormalGroup.coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4ddb49f2-69b6-5a93-8b6b-d79456edeb2d

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate

set_option autoImplicit false

open MvPowerSeries

universe u

namespace IterDeriv

variable {R : Type u} [CommRing R] {d : ℕ}

section Split

variable {α : Type*} [Finite α]

private theorem coeff_sumElim_rename_inl (g : MvPowerSeries α R) (m : α →₀ ℕ) (n : Fin d →₀ ℕ) :
    coeff (m.sumElim n) (rename (Sum.inl : α → α ⊕ Fin d) g) = if n = 0 then coeff m g else 0 := by
  split_ifs with hn
  · subst hn
    rw [← Finsupp.embDomain_inl]
    exact coeff_embDomain_rename Function.Embedding.inl g m
  · apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ : ∃ t, n t ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (Finsupp.ext h)
    have h := DFunLike.congr_fun hx (Sum.inr t)
    rw [Finsupp.mapDomain_notin_range, Finsupp.sumElim_inr] at h
    · exact ht h.symm
    · rintro ⟨y, hy⟩
      cases hy

omit [Finite α] in
private theorem prod_X_inr_pow (b : Fin d →₀ ℕ) :
    (b.prod fun j e => (X (Sum.inr j) : MvPowerSeries (α ⊕ Fin d) R) ^ e) =
      monomial ((0 : α →₀ ℕ).sumElim b) 1 := by
  classical
  rw [MvPowerSeries.monomial_one_eq, ← Finsupp.embDomain_inr, Finsupp.embDomain_eq_mapDomain,
    Finsupp.prod_mapDomain_index_inj Function.Embedding.inr.injective]
  rfl

private noncomputable abbrev inlPart (E : (Fin d ⊕ Fin d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.comapDomain Sum.inl E Sum.inl_injective.injOn

private noncomputable abbrev inrPart (E : (Fin d ⊕ Fin d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.comapDomain Sum.inr E Sum.inr_injective.injOn

private theorem inlPart_sumElim (a b : Fin d →₀ ℕ) : inlPart (a.sumElim b) = a := by
  ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inl]

private theorem inrPart_sumElim (a b : Fin d →₀ ℕ) : inrPart (a.sumElim b) = b := by
  ext t; rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inr]

private noncomputable def θfam (g : Fin d → MvPowerSeries α R) :
    Fin d ⊕ Fin d → MvPowerSeries (α ⊕ Fin d) R :=
  Sum.elim (fun j => rename (Sum.inl : α → α ⊕ Fin d) (g j)) fun j => X (Sum.inr j)

variable (g : Fin d → MvPowerSeries α R)

private theorem constantCoeff_θfam (hg : ∀ j, (g j).constantCoeff = 0) (s : Fin d ⊕ Fin d) :
    (θfam g s).constantCoeff = 0 := by
  rcases s with j | j
  · show (rename Sum.inl (g j)).constantCoeff = 0
    rw [constantCoeff_rename, hg]
  · exact constantCoeff_X _

private theorem coeff_sumElim_prod_θfam (μ : α →₀ ℕ) (ν : Fin d →₀ ℕ) (E : (Fin d ⊕ Fin d) →₀ ℕ) :
    coeff (μ.sumElim ν) (E.prod fun s e => θfam g s ^ e) =
      if inrPart E = ν then coeff μ ((inlPart E).prod fun j e => g j ^ e) else 0 := by
  classical
  obtain ⟨a, b, rfl⟩ : ∃ a b : Fin d →₀ ℕ, E = a.sumElim b :=
    ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain E).symm⟩
  rw [inlPart_sumElim, inrPart_sumElim, Finsupp.prod_sumElim]
  have h1 : (a.prod fun l e => ((fun s e => θfam g s ^ e) ∘ Sum.inl) l e) =
      rename (Sum.inl : α → α ⊕ Fin d) (a.prod fun l e => g l ^ e) := by
    rw [map_finsuppProd]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [Function.comp_apply, map_pow]
    rfl
  have h2 : (b.prod fun l e => ((fun s e => θfam g s ^ e) ∘ Sum.inr) l e) =
      monomial ((0 : α →₀ ℕ).sumElim b) 1 := by
    rw [← prod_X_inr_pow]
    rfl
  rw [h1, h2, coeff_mul_monomial, mul_one]
  by_cases hb : b ≤ ν
  · have hle : (0 : α →₀ ℕ).sumElim b ≤ μ.sumElim ν := by
      intro s; rcases s with t | t
      · rw [Finsupp.sumElim_inl, Finsupp.sumElim_inl]; exact Nat.zero_le _
      · rw [Finsupp.sumElim_inr, Finsupp.sumElim_inr]; exact hb t
    have hsub : μ.sumElim ν - (0 : α →₀ ℕ).sumElim b = μ.sumElim (ν - b) := by
      ext s; rcases s with t | t
      · rw [Finsupp.tsub_apply, Finsupp.sumElim_inl, Finsupp.sumElim_inl, Finsupp.sumElim_inl,
          Finsupp.zero_apply, Nat.sub_zero]
      · rw [Finsupp.tsub_apply, Finsupp.sumElim_inr, Finsupp.sumElim_inr, Finsupp.sumElim_inr,
          Finsupp.tsub_apply]
    rw [if_pos hle, hsub, coeff_sumElim_rename_inl]
    by_cases hbe : b = ν
    · subst hbe; rw [tsub_self, if_pos rfl, if_pos rfl]
    · rw [if_neg, if_neg hbe]
      intro h
      exact hbe (le_antisymm hb (tsub_eq_zero_iff_le.mp h))
  · rw [if_neg, if_neg]
    · intro h; exact hb (le_of_eq h)
    · intro h; exact hb fun t => by simpa using h (Sum.inr t)

private noncomputable def linB (i : Fin d) (K : MvPowerSeries (Fin d ⊕ Fin d) R) :
    MvPowerSeries (Fin d) R :=
  fun a => coeff (a.sumElim (Finsupp.single i 1)) K

private theorem coeff_linB (i : Fin d) (K : MvPowerSeries (Fin d ⊕ Fin d) R) (a : Fin d →₀ ℕ) :
    coeff a (linB i K) = coeff (a.sumElim (Finsupp.single i 1)) K := rfl

private theorem coeff_sumElim_single_subst_θfam (hg : ∀ j, (g j).constantCoeff = 0) (i : Fin d)
    (K : MvPowerSeries (Fin d ⊕ Fin d) R) (μ : α →₀ ℕ) :
    coeff (μ.sumElim (Finsupp.single i 1)) (subst (θfam g) K) = coeff μ (subst g (linB i K)) := by
  classical
  have hθ : HasSubst (θfam g) := hasSubst_of_constantCoeff_zero (constantCoeff_θfam g hg)
  have hgS : HasSubst g := hasSubst_of_constantCoeff_zero hg
  rw [coeff_subst hθ, coeff_subst hgS]

  let emb : (Fin d →₀ ℕ) → (Fin d ⊕ Fin d) →₀ ℕ := fun a => a.sumElim (Finsupp.single i 1)
  have hemb : Function.Injective emb := fun a a' h => by
    have := congrArg inlPart h
    rwa [inlPart_sumElim, inlPart_sumElim] at this
  let f' : ((Fin d ⊕ Fin d) →₀ ℕ) → R := fun E =>
    coeff (inlPart E) (linB i K) • coeff μ ((inlPart E).prod fun j e => g j ^ e)
  have hterm : ∀ E, coeff E K • coeff (μ.sumElim (Finsupp.single i 1)) (E.prod fun s e => θfam g s ^ e)
      = (Set.range emb).indicator f' E := by
    intro E
    rw [coeff_sumElim_prod_θfam, Set.indicator_apply]
    by_cases hE : inrPart E = Finsupp.single i 1
    · have hEeq : E = emb (inlPart E) := by
        show E = (inlPart E).sumElim (Finsupp.single i 1)
        rw [← hE]; exact (Finsupp.comapDomain_sumElim_comapDomain E).symm
      rw [if_pos hE, if_pos ⟨_, hEeq.symm⟩]
      show _ = coeff (inlPart E) (linB i K) • _
      rw [coeff_linB]
      congr 1
      rw [← hE, Finsupp.comapDomain_sumElim_comapDomain]
    · rw [if_neg hE, smul_zero, if_neg]
      rintro ⟨a, rfl⟩
      exact hE (inrPart_sumElim _ _)
  simp_rw [hterm]
  rw [← finsum_mem_def, finsum_mem_range hemb]
  refine finsum_congr fun a => ?_
  simp only [f', emb, inlPart_sumElim]

end Split

section Blocks

variable (n d : ℕ)

private def blockEquiv : (Fin n × Fin d) ⊕ Fin d ≃ Fin (n + 1) × Fin d where
  toFun := Sum.elim (fun sj => (Fin.castSucc sj.1, sj.2)) fun j => (Fin.last n, j)
  invFun sj := if h : sj.1 = Fin.last n then Sum.inr sj.2 else Sum.inl (sj.1.castPred h, sj.2)
  left_inv s := by
    rcases s with ⟨s, j⟩ | j
    · simp only [Sum.elim_inl, Fin.castSucc_ne_last, ↓reduceDIte, Fin.castPred_castSucc]
    · simp only [Sum.elim_inr, ↓reduceDIte]
  right_inv sj := by
    obtain ⟨s, j⟩ := sj
    by_cases h : s = Fin.last n
    · subst h; simp
    · simp only [h, ↓reduceDIte, Sum.elim_inl, Fin.castSucc_castPred]

private theorem blockEquiv_inl (sj : Fin n × Fin d) :
    blockEquiv n d (Sum.inl sj) = (Fin.castSucc sj.1, sj.2) := rfl

private theorem blockEquiv_inr (j : Fin d) : blockEquiv n d (Sum.inr j) = (Fin.last n, j) := rfl

end Blocks

private theorem rename_subst {σ τ τ' : Type*} [Finite σ] (f : τ → τ') [Filter.TendstoCofinite f]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, (a s).constantCoeff = 0) (K : MvPowerSeries σ R) :
    rename f (subst a K) = subst (fun s => rename f (a s)) K := by
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (HasSubst.X_comp f)]
  congr 1
  funext s
  rw [rename_eq_subst]

end IterDeriv

open IterDeriv in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞)
    (G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞)
    (hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k))
    (hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k))
    (i : Fin d) (L : MvPowerSeries (Fin d) 𝓞 → MvPowerSeries (Fin d) 𝓞)
    (hL : ∀ (H : MvPowerSeries (Fin d) 𝓞) (a : Fin d →₀ ℕ),
      (L H).coeff a = (subst F.toPowerSeries H).coeff (a.sumElim (Finsupp.single i 1)))
    (n : ℕ) (hn : 1 ≤ n) (H : MvPowerSeries (Fin d) 𝓞) :
    (subst (G n) H).coeff (∑ s : Fin n, Finsupp.single (s, i) 1) = (L^[n] H).constantCoeff := by
  classical
  have hFS : HasSubst F.toPowerSeries := hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero

  have hLeq : ∀ H' : MvPowerSeries (Fin d) 𝓞, L H' = IterDeriv.linB i (subst F.toPowerSeries H') :=
    fun H' => by ext a; rw [hL, IterDeriv.coeff_linB]

  have hG0 : ∀ n : ℕ, 1 ≤ n → ∀ k, (G n k).constantCoeff = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro k; rw [hG1]; exact constantCoeff_X _
    | succ n hn IH =>
      intro k
      rw [hGsucc]
      refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (F.constantCoeff_eq_zero k)
      all_goals
        rintro (j | j)
        · show (subst _ (G n j)).constantCoeff = 0
          exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
            (fun _ => constantCoeff_X _) (IH j)
        · exact constantCoeff_X _

  induction n, hn using Nat.le_induction generalizing H with
  | base =>

    have hemb : Function.Injective (fun k : Fin d => ((0 : Fin 1), k)) := fun a b h => (Prod.mk.inj h).2
    let emb0 : Fin d ↪ Fin 1 × Fin d := ⟨_, hemb⟩
    have hG1' : G 1 = X ∘ emb0 := funext hG1
    rw [Function.iterate_one, Fin.sum_univ_one, hG1', ← rename_eq_subst,
      ← coeff_zero_eq_constantCoeff_apply, hL]
    have e1 : (Finsupp.single ((0 : Fin 1), i) 1 : Fin 1 × Fin d →₀ ℕ) =
        Finsupp.embDomain emb0 (Finsupp.single i 1) := by
      rw [Finsupp.embDomain_single]; rfl
    rw [e1, coeff_embDomain_rename emb0 H (Finsupp.single i 1)]
    have e2 : ((0 : Fin d →₀ ℕ).sumElim (Finsupp.single i 1) : (Fin d ⊕ Fin d) →₀ ℕ) =
        Finsupp.single (Sum.inr i) 1 := by
      rw [← Finsupp.embDomain_inr, Finsupp.embDomain_single]; rfl
    rw [e2, MvFormalGroup.coeff_single_subst F.constantCoeff_eq_zero H (Sum.inr i)]
    simp only [F.coeff_single_inr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  | succ n hn IH =>

    have hGn0 : ∀ k, (G n k).constantCoeff = 0 := hG0 n hn
    set θ := IterDeriv.θfam (G n) with hθdef
    have hθ0 : ∀ s, (θ s).constantCoeff = 0 := IterDeriv.constantCoeff_θfam (G n) hGn0
    set e := IterDeriv.blockEquiv n d with hedef

    have hτ : (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞))) =
        fun s => rename e (θ s) := by
      funext s
      rcases s with j | j
      · show subst _ (G n j) = rename e (rename Sum.inl (G n j))
        rw [rename_rename, rename_eq_subst]
        rfl
      · show (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞) = rename e (X (Sum.inr j))
        rw [rename_X]
        rfl
    have hGs : ∀ k, G (n + 1) k = rename e (subst θ (F.toPowerSeries k)) := fun k => by
      rw [hGsucc, hτ, IterDeriv.rename_subst e hθ0]
    have hGfun : G (n + 1) = fun k => rename e (subst θ (F.toPowerSeries k)) := funext hGs

    have hθS : HasSubst θ := hasSubst_of_constantCoeff_zero hθ0
    have hcomp : subst (G (n + 1)) H = rename e (subst θ (subst F.toPowerSeries H)) := by
      rw [hGfun, ← IterDeriv.rename_subst e (fun k => constantCoeff_subst_eq_zero hθS hθ0
        (F.constantCoeff_eq_zero k)), subst_comp_subst_apply hFS hθS]

    have hexp : (∑ s : Fin (n + 1), Finsupp.single (s, i) 1 : Fin (n + 1) × Fin d →₀ ℕ) =
        Finsupp.embDomain e.toEmbedding
          ((∑ s : Fin n, Finsupp.single (s, i) 1 : Fin n × Fin d →₀ ℕ).sumElim (Finsupp.single i 1)) := by
      rw [Finsupp.embDomain_eq_mapDomain, Finsupp.sumElim_eq_add, Finsupp.mapDomain_add,
        ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, Finsupp.mapDomain_finsetSum,
        Fin.sum_univ_castSucc, Finsupp.mapDomain_single]
      simp only [Finsupp.mapDomain_single, Function.comp_apply, Equiv.coe_toEmbedding]
      rfl
    have key := coeff_embDomain_rename e.toEmbedding (subst θ (subst F.toPowerSeries H))
      ((∑ s : Fin n, Finsupp.single (s, i) 1 : Fin n × Fin d →₀ ℕ).sumElim (Finsupp.single i 1))
    simp only [Equiv.coe_toEmbedding] at key
    rw [hcomp, hexp, key, IterDeriv.coeff_sumElim_single_subst_θfam (G n) hGn0 i, ← hLeq, IH (L H),
      ← Function.iterate_succ_apply L n H]

end S_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
end P2MW
export P2MW.S_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate (solution)
