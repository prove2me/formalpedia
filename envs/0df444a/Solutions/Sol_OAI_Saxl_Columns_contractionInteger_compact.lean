-- Prove2me | solution 1 for OAI.Saxl.Columns.contractionInteger_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:33:27.82921+00:00
-- url     : https://prove2.me/submissions/b5625f68-c5bf-495f-a7f4-0a51d2725f16

import Mathlib
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma Domains.full_weight {rs : List ℕ} (σ : Perms rs) :
    (full rs).weight σ = sgInteger σ := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full, weight, sgInteger, Finset.mem_univ, ite_true, if_true, ih]

lemma Domains.atValue_weight {rs : List ℕ} (D : Domains rs) (c : Cells rs)
    (j : ℕ) (σ : Perms rs) :
    (D.atValue c j).weight σ = D.weight σ *
      (if row (perm σ c) = j then 1 else 0) := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    cases c with
    | inl i =>
      simp only [atValue, weight, Finset.mem_filter, perm, Equiv.sumCongr_apply,
        Sum.map_inl, row]
      split_ifs <;> simp_all
    | inr c =>
      simp only [atValue, weight, perm, Equiv.sumCongr_apply, Sum.map_inr, row, ih,
        mul_assoc]

lemma Domains.weight_eq_zero {rs : List ℕ} (D : Domains rs)
    (h : D.vanished = true) (σ : Perms rs) : D.weight σ = 0 := by
  induction rs with
  | nil => simp [vanished] at h
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    simp only [vanished, Bool.or_eq_true] at h
    rcases h with h | h
    · have hs : s = ∅ := of_decide_eq_true h
      simp [weight, hs]
    · simp only [weight, ih D h σ, mul_zero]

lemma Domains.mass_eq_sum {rs : List ℕ} (D : Domains rs) :
    D.mass = ∑ σ : Perms rs, D.weight σ := by
  classical
  induction rs with
  | nil => simp [mass, weight, Perms]
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [Perms, Fintype.sum_prod_type, weight, ← Finset.mul_sum, ← ih,
      ← Finset.sum_mul, mass]
    congr 1
    simp

lemma domainContraction_nil {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F [] flag = D.mass * E.mass * F.mass := by
  simp only [domainContraction, List.map_nil, List.prod_nil, mul_one,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Domains.mass_eq_sum]

lemma domainContraction_zero {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : (D.vanished || E.vanished || F.vanished) = true) :
    domainContraction D E F edges flag = 0 := by
  rw [domainContraction]
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · simp only [Domains.weight_eq_zero D h, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero E h, mul_zero, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero F h, mul_zero, zero_mul, Finset.sum_const_zero]

lemma triple_indicator_sum (flag : Finset (ℕ × ℕ × ℕ)) (a b c : ℕ) :
    (∑ v ∈ flag, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0)) =
      if (a,b,c) ∈ flag then 1 else 0 := by
  have hh : ∀ v : ℕ × ℕ × ℕ, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0) =
      if (a,b,c) = v then 1 else 0 := by
    rintro ⟨x,y,z⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [hh]
  rw [Finset.sum_ite_eq]

lemma domainContraction_cons {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  classical
  simp only [domainContraction, List.map_cons, List.prod_cons, Domains.atValue_weight]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  trans (D.weight π * E.weight σ * F.weight τ) *
    (∑ v ∈ flag, (if row (perm π c.1) = v.1 then (1 : ℤ) else 0) *
      (if row (perm σ c.2.1) = v.2.1 then 1 else 0) *
      (if row (perm τ c.2.2) = v.2.2 then 1 else 0)) *
    (edges.map (fun e => if (row (perm π e.1), row (perm σ e.2.1),
      row (perm τ e.2.2)) ∈ flag then (1 : ℤ) else 0)).prod
  · rw [triple_indicator_sum]
    ring
  · simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring

lemma domainContraction_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    {cs es : List (Edge rsT rsA rsB)} (hp : cs.Perm es)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F cs flag = domainContraction D E F es flag := by
  simp only [domainContraction]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  exact congrArg (_ * ·) ((hp.map _).prod_eq)

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Solver. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma domainContraction_cons_options {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ edgeOptions D E F c flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  rw [domainContraction_cons, edgeOptions, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with h
  · rfl
  · apply domainContraction_zero
    simpa only [Bool.or_eq_true, Bool.not_eq_false, not_and_or, or_assoc] using h

lemma bringBest_perm {α : Type*} (score : α → ℕ) (cs : List α) :
    (bringBest score cs).Perm cs := by
  induction cs with
  | nil => exact List.Perm.refl _
  | cons c cs ih =>
    rw [bringBest]
    cases he : bringBest score cs with
    | nil =>
      rw [he] at ih
      exact List.Perm.cons c ih
    | cons d ds =>
      rw [he] at ih
      simp only
      split_ifs
      · exact List.Perm.cons c ih
      · exact (List.Perm.swap _ _ _).trans (List.Perm.cons c ih)

lemma orderEdges_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    (orderEdges D E F edges flag).Perm edges := bringBest_perm _ _

theorem solveDomains_correct {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : edges.length ≤ fuel) :
    solveDomains fuel D E F edges flag = domainContraction D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    have hh : orderEdges D E F edges flag = [] := by
      apply List.length_eq_zero_iff.mp
      rw [(orderEdges_perm D E F edges flag).length_eq]
      omega
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · rw [hh]
      rw [← domainContraction_perm D E F (orderEdges_perm D E F edges flag) flag, hh]
      exact (domainContraction_nil D E F flag).symm
  | succ fuel ih =>
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · have hp := orderEdges_perm D E F edges flag
      rw [← domainContraction_perm D E F hp flag]
      cases he : orderEdges D E F edges flag with
      | nil => exact (domainContraction_nil D E F flag).symm
      | cons c cs =>
        have hlen : cs.length ≤ fuel := by
          have hl := hp.length_eq
          rw [he, List.length_cons] at hl
          omega
        rw [domainContraction_cons_options]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih _ _ _ _ hlen

lemma contractionInteger_domains {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      domainContraction (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  simp only [contractionInteger, domainContraction, Domains.full_weight,
    certificateEdges, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

theorem contractionInteger_solve {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveDomains n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [solveDomains_correct n _ _ _ _ _ (by simp [certificateEdges])]
  exact contractionInteger_domains ..

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_VectorDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma permVector_get {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (permVector π)[i.val]?.getD 0 = (π i).val := by
  simp [permVector,i.isLt]

lemma sign_eq_aux {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = Equiv.Perm.signAux π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => simp [Equiv.Perm.signAux_one]
  | swap_mul π i j hij ih =>
    rw [Equiv.Perm.sign_mul,Equiv.Perm.signAux_mul,ih,
      Equiv.Perm.sign_swap hij,Equiv.Perm.signAux_swap hij]

lemma vectorSign_perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    vectorSign n (permVector π) = (Equiv.Perm.sign π : ℤ) := by
  rw [sign_eq_aux]
  simp only [vectorSign,Equiv.Perm.signAux,Units.coe_prod,permVector_get]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.le_def]
  split_ifs <;> rfl

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_CompactDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma CompactDomain.mem_describe {n : ℕ} (π σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    σ ∈ CompactDomain.describe (some (π,s)) ↔ ∀ i, i ∉ s → σ i = π i := by
  simp [describe]

lemma CompactDomain.describe_full (n : ℕ) : (full n).describe = Finset.univ := by
  ext σ; simp [full,mem_describe]

lemma CompactDomain.describe_atValue {n : ℕ} (D : CompactDomain n) (i : Fin n) (j : ℕ) :
    (D.atValue i j).describe = D.describe.filter (fun σ => (σ i).val = j) := by
  cases D with
  | none => simp [atValue,describe]
  | some ds =>
    rcases ds with ⟨π,s⟩
    ext σ
    simp only [Finset.mem_filter,mem_describe]
    by_cases hj : j < n
    · let k := π.symm ⟨j,hj⟩
      have hk : π k = ⟨j,hj⟩ := π.apply_symm_apply _
      by_cases hi : i ∈ s
      · by_cases hks : k ∈ s
        · simp only [atValue,dite_eq_left hj,ite_eq_left hi,show π.symm ⟨j,hj⟩ ∈ s from hks,
            ite_true, if_true,mem_describe]
          constructor
          · intro h
            constructor
            · intro x hx
              have hxi : x ≠ i := by intro he; subst x; exact hx hi
              have hxk : x ≠ π.symm ⟨j,hj⟩ := by intro he; subst x; exact hx hks
              simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxi hxk] using
                h x (by simp [hx])
            · have hh := h i (by simp)
              simpa [Equiv.Perm.mul_apply,k] using congrArg Fin.val hh
          · rintro ⟨h,hv⟩ x hx
            by_cases hxi : x = i
            · subst x
              simpa [Equiv.Perm.mul_apply,k] using (Fin.ext hv : σ i = ⟨j,hj⟩)
            · have hxs : x ∉ s := by simpa [Finset.mem_erase,hxi] using hx
              have hxk : x ≠ π.symm ⟨j,hj⟩ := by intro he; subst x; exact hxs hks
              simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxi hxk] using h x hxs
        · simp only [atValue,dite_eq_left hj,ite_eq_left hi,show π.symm ⟨j,hj⟩ ∉ s from hks,
            ite_false, if_false,describe,Finset.notMem_empty,false_iff,not_and]
          intro h hv
          have hki : k = i := σ.injective ((h k hks).trans (hk.trans (Fin.ext hv).symm))
          exact hks (hki.symm ▸ hi)
      · by_cases hv : (π i).val = j
        · simp only [atValue,dite_eq_left hj,ite_eq_right hi,ite_eq_left hv,mem_describe]
          exact ⟨fun h => ⟨h,(congrArg Fin.val (h i hi)).trans hv⟩,fun h => h.1⟩
        · simp only [atValue,dite_eq_left hj,ite_eq_right hi,ite_eq_right hv,describe,Finset.notMem_empty,
            false_iff,not_and]
          intro h he
          exact hv ((congrArg Fin.val (h i hi)).symm.trans he)
    · simp only [atValue,dite_eq_right hj,describe,Finset.notMem_empty,false_iff,not_and]
      intro h hv
      exact hj (hv ▸ (σ i).isLt)

lemma CompactDomain.describe_vanished {n : ℕ} (D : CompactDomain n) :
    decide (D.describe = ∅) = D.vanished := by
  cases D with
  | none => rfl
  | some ds =>
    rcases ds with ⟨π,s⟩
    have hh : π ∈ CompactDomain.describe (some (π,s)) := by simp only [mem_describe]; tauto
    have hn := Finset.ne_empty_of_mem hh
    simp only [hn,decide_false,vanished,Option.isNone_some]

lemma compact_sum_sign {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) =
      if s.card ≤ 1 then (Equiv.Perm.sign π : ℤ) else 0 := by
  by_cases hs : s.card ≤ 1
  · rw [ite_eq_left hs]
    have he : CompactDomain.describe (some (π,s)) = {π} := by
      ext σ
      rw [CompactDomain.mem_describe,Finset.mem_singleton]
      constructor
      · intro h
        apply Equiv.ext
        intro i
        by_cases hi : i ∈ s
        · let k := π.symm (σ i)
          have hk : π k = σ i := π.apply_symm_apply _
          by_cases hks : k ∈ s
          · have hki : k = i := Finset.card_le_one.mp hs k hks i hi
            exact (hki ▸ hk).symm
          · have hki : k = i := σ.injective ((h k hks).trans hk)
            exact (hki ▸ hk).symm
        · exact h i hi
      · rintro rfl i hi; rfl
    simp only [he,Finset.sum_singleton]
  · rw [ite_eq_right hs]
    obtain ⟨i,hi,k,hk,hik⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    let τ := Equiv.swap i k
    have ht : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hik
    have hm (σ : Equiv.Perm (Fin n)) :
        σ * τ ∈ CompactDomain.describe (some (π,s)) ↔
        σ ∈ CompactDomain.describe (some (π,s)) := by
      simp only [CompactDomain.mem_describe]
      have hh (x : Fin n) (hx : x ∉ s) : τ x = x := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro he; subst x; exact hx hi
        · intro he; subst x; exact hx hk
      simp only [Equiv.Perm.mul_apply]
      constructor <;> intro h x hx <;> simpa only [hh x hx] using h x hx
    have he : (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) =
        ∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign (σ * τ) : ℤ) := by
      apply Finset.sum_bij (fun σ _ => σ * τ)
      · intro σ hσ; exact (hm σ).mpr hσ
      · intro σ hσ ρ hρ h; exact mul_right_cancel h
      · intro σ hσ
        refine ⟨σ * τ,(hm σ).mpr hσ,?_⟩
        simp [τ,mul_assoc]
      · intro σ hσ
        simp [τ,mul_assoc]
    have hn : (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign (σ * τ) : ℤ)) =
        -(∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) := by
      simp only [Equiv.Perm.sign_mul,ht,Units.val_neg,mul_neg_one,
        Finset.sum_neg_distrib]
    omega

lemma CompactDomain.describe_mass {n : ℕ} (D : CompactDomain n) :
    (∑ σ ∈ D.describe, (Equiv.Perm.sign σ : ℤ)) = D.mass := by
  cases D with
  | none => simp [describe,mass]
  | some ds =>
    rcases ds with ⟨π,s⟩
    simp only [mass,vectorSign_perm,compact_sum_sign]

lemma CompactDomains.describe_full (rs : List ℕ) : (full rs).describe = Domains.full rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full,describe,Domains.full,CompactDomain.describe_full,ih]; rfl

lemma CompactDomains.describe_atValue {rs : List ℕ} (D : CompactDomains rs) (c : Cells rs) (j : ℕ) :
    (D.atValue c j).describe = D.describe.atValue c j := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    cases c with
    | inl i => simp only [atValue,describe,Domains.atValue,CompactDomain.describe_atValue]; rfl
    | inr c => simp only [atValue,describe,Domains.atValue,ih]; rfl

lemma CompactDomains.describe_vanished {rs : List ℕ} (D : CompactDomains rs) :
    D.describe.vanished = D.vanished := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [describe,Domains.vanished,vanished,CompactDomain.describe_vanished,ih]

lemma CompactDomains.describe_mass {rs : List ℕ} (D : CompactDomains rs) :
    D.describe.mass = D.mass := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [describe,Domains.mass,mass,CompactDomain.describe_mass,ih]

lemma compactEdgeOptions_describe {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) :
    edgeOptions D.describe E.describe F.describe c flag = compactEdgeOptions D E F c flag := by
  simp only [compactEdgeOptions,edgeOptions,← CompactDomains.describe_atValue,
    CompactDomains.describe_vanished]

lemma compactOrderEdges_describe {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    orderEdges D.describe E.describe F.describe edges flag = compactOrderEdges D E F edges flag := by
  simp only [compactOrderEdges,orderEdges,compactEdgeOptions_describe]

lemma solveCompact_describe {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    solveDomains fuel D.describe E.describe F.describe edges flag = solveCompact fuel D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    rw [solveCompact,solveDomains]
    simp only [CompactDomains.describe_vanished,compactOrderEdges_describe,CompactDomains.describe_mass]
    all_goals (split <;> rfl)
  | succ fuel ih =>
    rw [solveCompact,solveDomains]
    simp only [CompactDomains.describe_vanished,compactOrderEdges_describe,CompactDomains.describe_mass]
    split
    · rfl
    · cases he : compactOrderEdges D E F edges flag with
      | nil => rfl
      | cons c cs =>
        simp only [compactEdgeOptions_describe,← CompactDomains.describe_atValue,ih]

lemma contractionInteger_compact_oai {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveCompact n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [contractionInteger_solve,← CompactDomains.describe_full,← CompactDomains.describe_full,
    ← CompactDomains.describe_full,solveCompact_describe]

end Saxl.Columns

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Columns.contractionInteger_compact_oai := @OAI.Saxl.Columns.contractionInteger_compact_oai
