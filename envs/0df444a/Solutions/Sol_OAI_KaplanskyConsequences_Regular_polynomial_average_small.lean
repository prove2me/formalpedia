-- Prove2me | solution 1 for OAI.KaplanskyConsequences.Regular.polynomial_average_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:41:38.767755+00:00
-- url     : https://prove2.me/submissions/cc7a932b-aae9-4526-8dd4-18673278aea7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf005
import Definitions.Def_OAIQ15Sf011
import Theorems.Thm_OAI_KaplanskyConsequences_Regular_average_conjugated_partition_bound

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular



lemma prefix_disjoint {i j : ℤ} {s t : Bool} {w : FZ}
    (h : Prefix i s w) (k : Prefix j t w) : i = j ∧ s = t := by
  rcases h with ⟨u,hu⟩; rcases k with ⟨v,hv⟩
  simpa using (List.cons.inj (hu.symm.trans hv)).1

lemma prefix_mul_of_not_negative (i : ℤ) (w : FZ) (h : ¬ Prefix i false w) :
    Prefix i true (FreeGroup.of i * w) := by
  unfold Prefix at *
  rw [FreeGroup.toWord_mul,FreeGroup.toWord_of,List.singleton_append,FreeGroup.reduce.cons,
    FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => exact ⟨[],rfl⟩
  | cons z t =>
    rcases z with ⟨j,s⟩
    have hn : ¬ (i = j ∧ true = !s) := by
      rintro ⟨rfl,hs⟩
      cases s with
      | false => exact h ⟨t,hw⟩
      | true => simp at hs
    simp only [hn,ite_false]
    exact ⟨(j,s)::t,rfl⟩


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

lemma translate_zero (w : FZ) : translate 0 w = w := by
  have he : (translate 0).toMonoidHom = MonoidHom.id FZ := by
    apply FreeGroup.ext_hom; intro i; simp
  exact DFunLike.congr_fun he w
lemma translate_add (n m : ℤ) (w : FZ) : translate (n+m) w = translate n (translate m w) := by
  have he : (translate (n+m)).toMonoidHom = (translate n).toMonoidHom.comp (translate m).toMonoidHom := by
    apply FreeGroup.ext_hom; intro i; simp [add_comm,add_left_comm]
  exact DFunLike.congr_fun he w
lemma translate_one : translate 1 = shift := rfl
lemma translate_neg_one (w : FZ) : translate (-1) w = shift.symm w := by
  apply shift.injective
  rw [←translate_one,←translate_add]
  simpa using translate_zero w

lemma action_affine (w : F2) (v : FZ) : action w v = coordinate w * translate (exponent w) v := by
  induction w using OAI.freeGroupInductionOn generalizing v with
  | one => simp [coordinate,translate_zero]
  | of i =>
    fin_cases i
    · change action a v = coordinate a * translate (exponent a) v
      simp [translate_one]
    · change action b v = coordinate b * translate (exponent b) v
      simp [translate_zero]
  | inv_of i ih =>
    fin_cases i
    · change action a⁻¹ v = coordinate a⁻¹ * translate (exponent a⁻¹) v
      simp [translate_neg_one]
    · change action b⁻¹ v = coordinate b⁻¹ * translate (exponent b⁻¹) v
      simp [translate_zero]
  | mul x y hx hy =>
    have hc : coordinate (x*y) = coordinate x * translate (exponent x) (coordinate y) := by
      simp only [coordinate,map_mul,Equiv.Perm.mul_apply]
      exact hx (action y 1)
    simp only [map_mul,Equiv.Perm.mul_apply,hx,hy,hc,exponent_mul,translate_add,map_mul,mul_assoc]

lemma coordinate_mul (x y : F2) :
    coordinate (x*y) = coordinate x * translate (exponent x) (coordinate y) := by
  simp only [coordinate,map_mul,Equiv.Perm.mul_apply]
  exact action_affine x (action y 1)

lemma kernelMap_translate (n : ℤ) (v : FZ) :
    kernelMap (translate n v) = a^n*kernelMap v*a^(-n) := by
  induction v using OAI.freeGroupInductionOn with
  | one => simp
  | of i => simp [genZ,zpow_add]; group
  | inv_of i ih => simp only [map_inv]; rw [ih]; group
  | mul x y hx hy => rw [map_mul,map_mul,map_mul,hx,hy]; group

lemma normal_form (w : F2) : w = kernelMap (coordinate w) * a^(exponent w) := by
  induction w using OAI.freeGroupInductionOn with
  | one => simp
  | of i =>
    fin_cases i
    · change a = kernelMap (coordinate a) * a^(exponent a); simp
    · change b = kernelMap (coordinate b) * a^(exponent b); simp [genZ]
  | inv_of i ih =>
    fin_cases i
    · change a⁻¹ = kernelMap (coordinate a⁻¹) * a^(exponent a⁻¹); simp
    · change b⁻¹ = kernelMap (coordinate b⁻¹) * a^(exponent b⁻¹); simp [genZ]
  | mul x y hx hy =>
    rw [coordinate_mul,map_mul,kernelMap_translate,exponent_mul,zpow_add]
    calc
      x*y = (kernelMap (coordinate x)*a^(exponent x))*(kernelMap (coordinate y)*a^(exponent y)) := by rw [←hx,←hy]
      _ = _ := by group

lemma coordinate_exponent_separate (w : F2) (hc : coordinate w=1) (he : exponent w=0) : w=1 := by
  simpa [hc,he] using normal_form w

lemma action_genZ (n : ℤ) : action (genZ n) = Equiv.mulLeft (FreeGroup.of n) := by
  have ha (k : ℤ) (v : FZ) : action (a^k) v = translate k v := by
    have hp : action a ^ k = (translate k).toEquiv := by
      induction k using Int.induction_on with
      | zero => ext v; simp [translate_zero]
      | succ k ih =>
        ext v
        rw [zpow_add,ih]
        simp only [zpow_one,action_a,Equiv.Perm.mul_apply]
        exact (translate_add k 1 v).symm
      | pred k ih =>
        ext v
        rw [zpow_sub,ih]
        simp only [zpow_one,action_a,Equiv.Perm.mul_apply]
        change translate (-(k:ℤ)) (shift.symm v) = translate (-(k:ℤ)-1) v
        rw [←translate_neg_one,←translate_add]
        rfl
    rw [map_zpow,hp]; rfl
  ext v
  simp only [genZ,map_mul,Equiv.Perm.mul_apply,ha,action_b]
  change translate n (FreeGroup.of 0 * translate (-n) v) = FreeGroup.of n * v
  rw [map_mul,translate_of,←translate_add]
  simp [translate_zero]

@[simp] lemma coordinate_genZ (n : ℤ) : coordinate (genZ n) = FreeGroup.of n := by
  simp [coordinate,action_genZ]
lemma coordinate_genZ_mul (n : ℤ) (w : F2) : coordinate (genZ n*w) = FreeGroup.of n*coordinate w := by
  simp [coordinate_mul,translate_zero]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

lemma toWord_translate (n : ℤ) (v : FZ) :
    (translate n v).toWord = v.toWord.map (fun x => (x.1+n,x.2)) := by
  have hr : FreeGroup.IsReduced (v.toWord.map (fun x => (x.1+n,x.2))) := by
    rw [FreeGroup.IsReduced,List.isChain_map]
    apply List.IsChain.imp (p:=FreeGroup.isReduced_toWord)
    intro x y h hxy
    exact h (add_right_cancel hxy)
  conv_lhs => rw [←FreeGroup.mk_toWord (x:=v)]
  change ((FreeGroup.map (fun i : ℤ => i+n)) (FreeGroup.mk v.toWord)).toWord = _
  rw [FreeGroup.map.mk,FreeGroup.toWord_mk,hr.reduce_eq]

lemma toWord_mul_of_boundary (v w : FZ)
    (hb : ∀ x ∈ v.toWord.getLast?, ∀ y ∈ w.toWord.head?, x.1 ≠ y.1) :
    (v*w).toWord = v.toWord ++ w.toWord := by
  rw [FreeGroup.toWord_mul]
  apply FreeGroup.IsReduced.reduce_eq
  exact List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
    (fun x hx y hy hxy => (hb x hx y hy hxy).elim)

lemma toWord_inv_of (n : ℤ) : (FreeGroup.of n : FZ)⁻¹.toWord = [(n,false)] := by
  simp [FreeGroup.toWord_inv,FreeGroup.toWord_of,FreeGroup.invRev]

lemma starts_iff_head (n : ℤ) (v : FZ) : Starts n v ↔ ∃ s, (n,s) ∈ v.toWord.head? := by
  simp only [Starts,Prefix,Option.mem_def,List.head?_eq_some_iff]
lemma not_starts_head {n : ℤ} {v : FZ} (h : ¬ Starts n v) {x : ℤ × Bool}
    (hx : x ∈ v.toWord.head?) : x.1 ≠ n := by
  intro he
  apply h
  apply (starts_iff_head _ _).2
  exact ⟨x.2,by simpa [←he] using hx⟩

lemma starts_translate (n k : ℤ) (v : FZ) :
    Starts (n+k) (translate k v) ↔ Starts n v := by
  rw [starts_iff_head,starts_iff_head,toWord_translate]
  simp only [List.head?_map,Option.mem_map]
  constructor
  · rintro ⟨s,x,hx,he⟩
    have hx1 : x.1=n := add_right_cancel (congrArg Prod.fst he)
    have hx2 : x.2=s := congrArg Prod.snd he
    have hx' : x = (n,s) := Prod.ext hx1 hx2
    exact ⟨s,by simpa [hx'] using hx⟩
  · rintro ⟨s,hs⟩
    exact ⟨s,(n,s),hs,rfl⟩

lemma prefix_multiply_of_not_starts (n : ℤ) (v : FZ) (h : ¬ Starts n v) :
    Prefix n true (FreeGroup.of n*v) :=
  prefix_mul_of_not_negative n v (fun hp => h ⟨false,hp⟩)

lemma word_sandwich (n k : ℤ) (v : FZ)
    (h1 : ∀ x ∈ v.toWord, x.1 ≠ n)
    (h2 : ∀ x ∈ v.toWord, x.1 ≠ n+k)
    (hne : v ≠ 1 ∨ k ≠ 0) :
    (FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹).toWord =
      [(n,true)] ++ v.toWord ++ [(n+k,false)] := by
  have hleft : (FreeGroup.of n*v).toWord = [(n,true)] ++ v.toWord := by
    rw [toWord_mul_of_boundary,FreeGroup.toWord_of]
    intro x hx y hy
    simp only [FreeGroup.toWord_of,List.getLast?_singleton,Option.mem_some_iff] at hx
    subst x
    exact (h1 y (List.mem_of_mem_head? hy)).symm
  rw [toWord_mul_of_boundary,hleft,toWord_inv_of]
  intro x hx y hy
  simp only [toWord_inv_of,List.head?_cons,Option.mem_some_iff] at hy
  subst y
  rw [hleft,List.getLast?_append] at hx
  by_cases hv : v=1
  · subst v
    simp only [FreeGroup.toWord_one,List.getLast?_nil,Option.none_or,List.getLast?_singleton,
      Option.mem_some_iff] at hx
    subst x
    intro he
    have hk : k=0 := by omega
    exact hne.elim (fun h => h rfl) (fun h => h hk)
  · have ht : v.toWord.getLast? ≠ none := by
      simpa only [ne_eq,List.getLast?_eq_none_iff,FreeGroup.toWord_eq_nil_iff] using hv
    cases hvw : v.toWord.getLast? with
    | none => exact (ht hvw).elim
    | some z =>
      rw [hvw,Option.some_or] at hx
      exact h2 x (List.mem_of_mem_getLast? (by simpa [hvw] using hx))

lemma sandwich_multiply_starts (n k : ℤ) (v w : FZ)
    (h1 : ∀ x ∈ v.toWord, x.1 ≠ n)
    (h2 : ∀ x ∈ v.toWord, x.1 ≠ n+k)
    (hne : v ≠ 1 ∨ k ≠ 0) (hw : ¬ Starts n w) :
    Starts n ((FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹)*translate k w) := by
  have hs := word_sandwich n k v h1 h2 hne
  have ht : ¬ Starts (n+k) (translate k w) := by rwa [starts_translate]
  have he : ((FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹)*translate k w).toWord =
      (FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹).toWord ++ (translate k w).toWord := by
    apply toWord_mul_of_boundary
    intro x hx y hy
    simp only [hs,List.getLast?_append,List.getLast?_singleton,Option.some_or,
      Option.mem_some_iff] at hx
    subst x
    exact (not_starts_head ht hy).symm
  refine ⟨true,?_⟩
  unfold Prefix
  rw [he,hs]
  exact ⟨v.toWord ++ [(n+k,false)] ++ (translate k w).toWord,by simp [List.append_assoc]⟩


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma conjugateMap_val (g : G) (x : Algebra G) :
    (conjugateMap g x).val = left g*x.val*left g⁻¹ := rfl

lemma mask_left_mask_zero (D : G → Prop) (f : G)
    (hD : ∀ w, D w → ¬D (f*w)) :
    mask (H:=ℂ) D*left f*mask D = 0 := by
  ext x w
  simp only [mul_apply_eq_comp,mask_apply,left_apply,zero_apply,lp.coeFn_zero,Pi.zero_apply]
  by_cases hw : D w
  · have hf : ¬D (f⁻¹*w) := by
      intro hf
      have hk := hD (f⁻¹*w) hf
      simp only [mul_inv_cancel_left] at hk
      exact hk hw
    simp only [ite_eq_left hw,ite_eq_right hf]
  · simp only [ite_eq_right hw]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

lemma starts_index_unique {n m : ℤ} {v : FZ} (hn : Starts n v) (hm : Starts m v) : n=m := by
  obtain ⟨s,hs⟩ := hn
  obtain ⟨t,ht⟩ := hm
  exact (prefix_disjoint hs ht).1

lemma coordinate_genZ_inv (n : ℤ) : coordinate (genZ n)⁻¹ = (FreeGroup.of n)⁻¹ := by
  simp [coordinate,map_inv,action_genZ]
lemma coordinate_conjugate (n : ℤ) (w : F2) :
    coordinate (genZ n*w*(genZ n)⁻¹) = FreeGroup.of n*coordinate w*(FreeGroup.of (n+exponent w))⁻¹ := by
  simp [coordinate_mul,coordinate_genZ_inv,translate_zero]

theorem powers_partition (F : Finset F2) (hF : ∀ f ∈ F, f ≠ 1) (N : ℕ) :
    ∃ (u : F2) (D : F2 → Prop) (h : Fin N → F2),
      (∀ f ∈ F, ∀ w, D w → ¬ D (u*f*u⁻¹*w)) ∧
      (∀ i j w, ¬ D ((h i)⁻¹*w) → ¬ D ((h j)⁻¹*w) → i=j) := by
  let S : Finset ℤ := F.biUnion (fun f =>
    ((coordinate f).toWord.map Prod.fst).toFinset ∪
    ((coordinate f).toWord.map (fun z => z.1-exponent f)).toFinset)
  obtain ⟨n,hn⟩ := S.exists_notMem
  have h1 (f : F2) (hf : f ∈ F) (x : ℤ × Bool) (hx : x ∈ (coordinate f).toWord) : x.1 ≠ n := by
    intro he
    apply hn
    apply Finset.mem_biUnion.mpr
    refine ⟨f,hf,Finset.mem_union_left _ ?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,he⟩)
  have h2 (f : F2) (hf : f ∈ F) (x : ℤ × Bool) (hx : x ∈ (coordinate f).toWord) : x.1 ≠ n+exponent f := by
    intro he
    apply hn
    apply Finset.mem_biUnion.mpr
    refine ⟨f,hf,Finset.mem_union_right _ ?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,by omega⟩)
  let D : F2 → Prop := fun w => ¬ Starts n (coordinate w)
  let h : Fin N → F2 := fun i => genZ (n+(i.val:ℤ)+1)
  refine ⟨genZ n,D,h,?_,?_⟩
  · intro f hf w hw
    change ¬¬ Starts n (coordinate (genZ n*f*(genZ n)⁻¹*w))
    apply not_not.mpr
    rw [coordinate_mul,coordinate_conjugate]
    have hk : exponent (genZ n*f*(genZ n)⁻¹) = exponent f := by simp
    rw [hk]
    apply sandwich_multiply_starts n (exponent f) (coordinate f) (coordinate w) (h1 f hf) (h2 f hf) _ hw
    by_contra he
    push Not at he
    exact hF f hf (coordinate_exponent_separate f he.1 he.2)
  · intro i j w hi hj
    have hs (k : Fin N) (hk : ¬D ((h k)⁻¹*w)) : Starts (n+(k.val:ℤ)+1) (coordinate w) := by
      have hp : Starts n (coordinate ((h k)⁻¹*w)) := not_not.mp hk
      have hn' : ¬ Starts (n+(k.val:ℤ)+1) (coordinate ((h k)⁻¹*w)) := by
        intro ht
        have he := starts_index_unique ht hp
        have hk0 : (0:ℤ) ≤ k.val := Int.natCast_nonneg _
        omega
      have he := coordinate_genZ_mul (n+(k.val:ℤ)+1) ((h k)⁻¹*w)
      change coordinate (h k*((h k)⁻¹*w)) = _ at he
      simp only [mul_inv_cancel_left] at he
      rw [he]
      exact ⟨true,prefix_multiply_of_not_starts _ _ hn'⟩
    have he := starts_index_unique (hs i hi) (hs j hj)
    apply Fin.ext
    omega


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]
lemma polynomial_apply (c : G →₀ ℂ) :
    (polynomial c).val = ∑ g ∈ c.support, c g • left g := by
  simp only [polynomial,Finsupp.linearCombination_apply,Finsupp.sum]
  change (Algebra G).subtype (∑ g ∈ c.support, c g • generator g) = _
  simp only [map_sum,map_smul]
  rfl


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_PowersAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
section
attribute [local instance 2000] Classical.propDecidable Classical.decEq

lemma conjugateMap_polynomial_val (u : F2) (c : F2 →₀ ℂ) :
    (conjugateMap u (polynomial c)).val = ∑ f ∈ c.support, c f • left (u*f*u⁻¹) := by
  rw [conjugateMap_val,polynomial_apply]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←left_mul,←left_mul]

lemma polynomial_mask_zero (u : F2) (D : F2 → Prop) (c : F2 →₀ ℂ)
    (hD : ∀ f ∈ c.support, ∀ w, D w → ¬D (u*f*u⁻¹*w)) :
    mask D*(conjugateMap u (polynomial c)).val*mask D=0 := by
  rw [conjugateMap_polynomial_val]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_eq_zero
  intro f hf
  rw [mask_left_mask_zero D (u*f*u⁻¹) (hD f hf)]
  exact smul_zero (A := HilbertSum F2 ℂ →L[ℂ] HilbertSum F2 ℂ) (c f)

lemma polynomial_average_bound (c : F2 →₀ ℂ) (hc : c 1=0) (N : ℕ) :
    ∃ h : Fin N → F2, ‖averageConjugate h (polynomial c)‖ ≤
      (N:ℝ)⁻¹*(2*Real.sqrt N*‖polynomial c‖) := by
  obtain ⟨u,D,h,hD,hd⟩ := powers_partition c.support
    (fun f hf he => Finsupp.mem_support_iff.mp hf (he ▸ hc)) N
  refine ⟨fun i => h i*u,?_⟩
  exact average_conjugated_partition_bound D h hd u (polynomial c)
    (polynomial_mask_zero u D c hD)

end

lemma polynomial_average_small_oai (c : F2 →₀ ℂ) (hc : c 1=0) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, 0<N ∧ ∃ h : Fin N → F2, ‖averageConjugate h (polynomial c)‖ < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 (2*‖polynomial c‖/ε))
  have hn0 : (0:ℝ)<n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 2*‖polynomial c‖ < (n:ℝ)*ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  obtain ⟨h,hh⟩ := polynomial_average_bound c hc (n^2)
  refine ⟨n^2,pow_pos (Nat.cast_pos.mp hn0) 2,h,lt_of_le_of_lt hh ?_⟩
  rw [Nat.cast_pow,Real.sqrt_sq (le_of_lt hn0)]
  calc
    _ = 2*‖polynomial c‖/(n:ℝ) := by field_simp
    _ < ε := (div_lt_iff₀ hn0).mpr (by simpa [mul_comm] using hn1)


end KaplanskyConsequences.Regular

end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.Regular.polynomial_average_small_oai := @OAI.KaplanskyConsequences.Regular.polynomial_average_small_oai
