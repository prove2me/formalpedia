-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:35:53.945617+00:00
-- url     : https://prove2.me/submissions/bc2d3155-de12-4ca3-a02b-eb1a94db0d25

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_OriginalRealCohenFactorization_real_factorization
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_real_hull_generic_column_realizes

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace UniformOracle

theorem runningSum_recursive {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n))) :
    Nat.RecursiveIn O (fun n => Part.some (runningSum f n)) := by
  have hy := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp (total_primrec (Primrec.nat_add.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hf hy))
  have hp := Nat.RecursiveIn.prec (total_primrec (Primrec.const 0)) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    change (Part.some (runningSum f n)).bind _ = _
    rw [Part.bind_some]
    rfl
end UniformOracle

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericCoding
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericCoding
open UniformOracle BinarySeries Encodable

theorem count_le (G : Oracle) (n : ℕ) : count G n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) ≤ n+1
    unfold bit
    split <;> omega

theorem count_recursive {O : Set (ℕ →. ℕ)} (G : Oracle)
    (hG : Nat.RecursiveIn O (oracleFunction G)) :
    Nat.RecursiveIn O (fun n => Part.some (count G n)) :=
  runningSum_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_comp hG (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))))

theorem code_recursive {O : Set (ℕ →. ℕ)} (A G : Oracle)
    (hA : Nat.RecursiveIn O (oracleFunction A)) (hG : Nat.RecursiveIn O (oracleFunction G)) :
    Nat.RecursiveIn O (oracleFunction (code A G)) := by
  have hc := count_recursive G hG
  have ho := _root_.OAI.TuringRigidity.UniformOracle.total_comp hG (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))
  have ha := _root_.OAI.TuringRigidity.UniformOracle.total_comp hA hc
  have hi := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hc)
  have he := _root_.OAI.TuringRigidity.UniformOracle.total_comp hG hi
  have hd : Primrec (fun z : ℕ => if (Nat.unpair z).1=1 then
      (Nat.unpair (Nat.unpair z).2).1 else (Nat.unpair (Nat.unpair z).2).2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hd) (_root_.OAI.TuringRigidity.UniformOracle.total_pair ho (_root_.OAI.TuringRigidity.UniformOracle.total_pair ha he))).of_eq (fun n => by
    cases hh : G (2*n+1) <;> simp [code,oracleFunction,hh])

theorem code_reduces (A G : Oracle) : Reduces (code A G) (join A G) := by
  apply RecursiveIn.iff_nat.mpr
  exact code_recursive A G (RecursiveIn.iff_nat.mp (reduces_join_left A G))
    (RecursiveIn.iff_nat.mp (reduces_join_right A G))

end TuringRigidity.GenericCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteShuffle
open GenericCoding UniformOracle BinarySeries

theorem Agree.mono {n m : ℕ} {A B : Oracle} (h : Agree n A B) (hm : m ≤ n) :
    Agree m A B := fun i hi => h i (by omega)

theorem Agree.trans {n : ℕ} {A B C : Oracle} (h : Agree n A B) (h' : Agree n B C) :
    Agree n A C := fun i hi => (h i hi).trans (h' i hi)

theorem prefix_agree {A B : Oracle} {n : ℕ} (h : Agree n A B) : initial A n = initial B n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < n := by simpa using hi
    simpa [initial] using h i hi'

theorem count_agree {n : ℕ} {G H : Oracle} (h : ∀ i, i < n → G (2*i+1) = H (2*i+1)) :
    count G n = count H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) = count H n + bit H (2*n+1)
    rw [ih (fun i hi => h i (by omega))]
    simp [bit,h n (by omega)]

theorem count_constant {n : ℕ} {G : Oracle} (h : OddBound n G) {m : ℕ} (hm : n ≤ m) :
    count G m = count G n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    change count G m + bit G (2*m+1) = count G n
    simp [bit,h m hm,ih]

theorem code_agree {n : ℕ} {A B G H : Oracle} (ha : Agree n A B) (hg : Agree (2*n) G H) :
    Agree n (code A G) (code B H) := by
  intro i hi
  have hc : count G i = count H i := count_agree (fun j hj => hg (2*j+1) (by omega))
  have ho := hg (2*i+1) (by omega)
  have hl := count_le G i
  simp only [code,←hc,←ho]
  split
  · exact ha _ (by omega)
  · exact hg _ (by omega)

theorem code_agree_inserted {n : ℕ} {A B G : Oracle} (hg : OddBound n G) (ha : Agree n A B) :
    code A G = code B G := by
  funext i
  unfold code
  split
  · rename_i hb
    have hi : i < n := by
      by_contra hi
      have := hg i (by omega)
      simp_all
    exact ha _ (lt_of_le_of_lt (count_le G i) hi)
  · rfl

theorem freeze_bound (n : ℕ) (G : Oracle) : OddBound n (freeze n G) := by
  intro i hi
  simp [freeze,show ¬i<n by omega]

theorem agree_of_columns {n : ℕ} {G H : Oracle}
    (he : ∀ i, i < n → G (2*i) = H (2*i))
    (ho : ∀ i, i < n → G (2*i+1) = H (2*i+1)) : Agree (2*n) G H := by
  intro i hi
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have hh : i = 2*(i/2) := by omega
    rw [hh]
    exact he _ (by omega)
  · have hh : i = 2*(i/2)+1 := by omega
    rw [hh]
    exact ho _ (by omega)

theorem freeze_agree (n : ℕ) (G : Oracle) : Agree (2*n) G (freeze n G) := by
  apply agree_of_columns
  · intro i hi; simp [freeze]
  · intro i hi; simp [freeze,hi]

theorem extendEven_count (n : ℕ) (G T : Oracle) (i : ℕ) :
    count (extendEven n G T) i = count G i :=
  count_agree (fun j hj => by simp [extendEven])

theorem extendEven_agree (n : ℕ) (G T : Oracle) : Agree (2*n) G (extendEven n G T) := by
  apply agree_of_columns
  · intro i hi; simp [extendEven,hi]
  · intro i hi; simp [extendEven]

theorem extendEven_code (n : ℕ) (A G T : Oracle) (hg : OddBound n G)
    (ht : Agree (n + count G n) (code A G) T) : code A (extendEven n G T) = T := by
  funext i
  simp only [code]
  rw [extendEven_count]
  simp only [extendEven,join_odd,join_even]
  have hcn := count_le G n
  by_cases hi : i < n + count G n
  · rw [←ht i hi]
    unfold code
    split
    · rfl
    · have hsub : i - count G i < n := by
        by_cases hin : i < n
        · omega
        · rw [count_constant hg (by omega)]
          omega
      simp [hsub]
  · have hin : n ≤ i := by omega
    have hc := count_constant hg hin
    rw [hg i hin]
    simp only [Bool.false_eq_true,↓reduceIte,hc]
    have hl := count_le G n
    have hn : ¬i-count G n<n := by omega
    rw [ite_eq_right hn]
    congr 1
    omega

theorem agree_of_prefix {A : Oracle} {n : ℕ} {t : List Bool} (h : initial A n <+: t) :
    Agree n A (fun i => t.getD i false) := by
  obtain ⟨u,hu⟩ := h
  intro i hi
  rw [←hu]
  simpa [List.getD,List.getElem?_append,hi] using (prefix_getD A n i hi).symm

theorem odd_null_extension (D : List Bool → Prop) (hd : DenseOpen D)
    (n : ℕ) (A G : Oracle) (hg : OddBound n G) :
    ∃ m H, n < m ∧ Agree (2*n) G H ∧
      (∀ i, H (2*i+1) = G (2*i+1)) ∧ D (initial (code A H) m) := by
  obtain ⟨t,ht,hD⟩ := hd.1 (initial (code A G) (n + count G n + 1))
  let T : Oracle := fun i => t.getD i false
  have ha : Agree (n + count G n) (code A G) T :=
    (agree_of_prefix ht).mono (by omega)
  have he := extendEven_code n A G T hg ha
  refine ⟨t.length,extendEven n G T,?_,extendEven_agree n G T,?_,?_⟩
  · have hl := ht.length_le
    simp only [prefix_length] at hl
    omega
  · intro i; simp [extendEven]
  · rw [he]
    change D (initial (fun i => t.getD i false) t.length)
    rw [prefix_default]
    exact hD

theorem finite_extension (D : List Bool → Prop) (hd : DenseOpen D)
    (S : Finset Oracle) (n : ℕ) (G : Oracle) (hg : OddBound n G) :
    ∃ m H, n ≤ m ∧ Agree (2*n) G H ∧
      (∀ i, H (2*i+1) = G (2*i+1)) ∧
      ∀ A ∈ S, ∃ l, l ≤ m ∧ D (initial (code A H) l) := by
  classical
  induction S using Finset.induction_on generalizing n G with
  | empty => exact ⟨n,G,le_rfl,fun _ _ => rfl,fun _ => rfl,by simp⟩
  | @insert A S hAS ih =>
    obtain ⟨m,H,hnm,hGH,hoH,hS⟩ := ih n G hg
    have hb : OddBound m H := by
      intro i hi
      rw [hoH i]
      exact hg i (by omega)
    obtain ⟨k,K,hmk,hHK,hoK,hD⟩ := odd_null_extension D hd m A H hb
    refine ⟨k,K,by omega,hGH.trans (hHK.mono (by omega)),
      fun i => (hoK i).trans (hoH i),?_⟩
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨k,le_rfl,hD⟩
    · obtain ⟨l,hl,hDl⟩ := hS B hB
      refine ⟨l,by omega,?_⟩
      have hc : Agree l (code B H) (code B K) :=
        code_agree (fun _ _ => rfl) (hHK.mono (by omega))
      rwa [←prefix_agree hc]

theorem all_extension (D : List Bool → Prop) (hd : DenseOpen D) (n : ℕ) (G : Oracle) :
    ∃ m H, n ≤ m ∧ Agree (2*n) G H ∧ OddBound n H ∧
      ∀ A, ∃ l, l ≤ m ∧ D (initial (code A H) l) := by
  classical
  let f : (Fin n → Bool) → Oracle := fun s i => if hi : i < n then s ⟨i,hi⟩ else false
  let S : Finset Oracle := Finset.univ.image f
  obtain ⟨m,H,hnm,hGH,ho,hS⟩ := finite_extension D hd S n (freeze n G) (freeze_bound n G)
  have hb : OddBound n H := fun i hi => (ho i).trans (freeze_bound n G i hi)
  refine ⟨m,H,hnm,(freeze_agree n G).trans hGH,hb,?_⟩
  intro A
  let a : Fin n → Bool := fun i => A i
  have ha : f a ∈ S := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  obtain ⟨l,hl,hD⟩ := hS (f a) ha
  have he : code (f a) H = code A H := code_agree_inserted hb (by
    intro i hi
    simp [f,a,hi])
  exact ⟨l,hl,by simpa [he] using hD⟩

end TuringRigidity.FiniteShuffle

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericFilterName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

theorem val_genericFilterName (p : ZFSet.{u}) [Top (Conditions p)]
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (genericFilterName p).val G = genericFilterSet p G := by
  apply ZFSet.ext; intro x
  simp only [genericFilterName,Name.mem_val,Name.val_check G hG,mem_genericFilterSet,id_eq]

theorem eval_filterCodeFormula (z p f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    filterCodeFormula.Eval (cons z (cons p (cons f (cons r e)))) ↔
      ∃ x ∈ p, ∃ v ∈ r, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  simp only [filterCodeFormula,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_filterCode (p f z : ZFSet.{u}) :
    z ∈ filterCode p f ↔ ∃ x ∈ p, ∃ v, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  rw [filterCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,v,_,hv,hz⟩; exact ⟨x,hx,v,hv,hz⟩
  · rintro ⟨x,hx,v,hv,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,x,hx,rfl⟩,x,hx,v,hr,hv,rfl⟩

theorem filterCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {p f : ZFSet.{u}} (hp : p ∈ M) (hf : f ∈ M) : filterCode p f ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons p (cons f (cons (iterUnion 2 f) (fun _ => p)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hp
    rcases i with _|i; exact hf
    rcases i with _|i; exact hr
    exact hp
  have hs := sep_mem M hM hS filterCodeFormula e he
    (product_mem M hM hP hU hPow hS hr hp)
  have heq : ZFSet.sep (fun z => filterCodeFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) p) = filterCode p f := by
    apply ZFSet.ext; intro z
    simp only [filterCode,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_filterCodeFormula z p f _ _)
  exact heq ▸ hs

theorem encode_genericFilterName (p d r f : ZFSet.{u}) [Top (Conditions p)]
    (hsub : p ⊆ d) (hf : CheckGraph d r f (label p ⊤)) :
    (genericFilterName p).encode (label p) = filterCode p f := by
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_filterCode]
  constructor
  · rintro ⟨q,hq⟩
    have hx := hsub (label_mem p q)
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 (label p q) hx
    have he := hf.correct _ hx v hv hfv
    refine ⟨label p q,label_mem p q,v,hfv,?_⟩
    simpa only [genericFilterName,id_eq,encode_check,he] using hq.symm
  · rintro ⟨x,hx,v,hfv,hz⟩
    obtain ⟨q,rfl⟩ := label_surjective p hx
    have hfr : FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
    have he := hf.correct _ (hsub hx) v (hfr.value_mem hfv) hfv
    exact ⟨q,by simpa only [genericFilterName,id_eq,encode_check,he] using hz.symm⟩

theorem genericFilterName_mem (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) : genericFilterName p ∈ names M p := by
  obtain ⟨d,hdM,hd,hpd⟩ := internal_transitive_container M hM hP hU hS hR hI hp
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label p ⊤) hM hP hU hPow hS hR
    hdM hqM (hM p hp _ (label_mem p ⊤)) hd hq p hpd
  have hsub : p ⊆ hull d q p := fun x hx =>
    hull_transitive d q p hd p (self_mem_hull d q hpd) x hx
  change (genericFilterName p).encode (label p) ∈ M
  rw [encode_genericFilterName p _ _ f hsub hfg]
  exact filterCode_mem M hM hP hU hPow hS hp hf

theorem genericFilterSet_mem_extension (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    genericFilterSet p G ∈ genericExtensionSet M p G :=
  (mem_extensionSet M p G _).mpr ⟨genericFilterName p,
    genericFilterName_mem M p hM hP hU hPow hS hR hI hp,val_genericFilterName p G hG⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenConditions
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

theorem conditions_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : conditions ∈ M := by
  obtain ⟨c,hc,hdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
    (alphabet_mem M hM hT)
  have he : c = conditions := ZFSet.ext (fun p => (hdef p).trans (mem_conditions p).symm)
  exact he ▸ hc

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

theorem omega_exists (P : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, P x) ↔ ∃ n, P (natSet n) := by
  constructor
  · rintro ⟨x,hx,hP⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,hP⟩
  · rintro ⟨n,hP⟩
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,hP⟩

end
end TuringRigidity.SetModelReals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem finiteGraph_zero (f : ℕ → ZFSet.{u}) : finiteGraph 0 f = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,Nat.not_lt_zero,false_and,exists_false,ZFSet.notMem_empty]

theorem finiteGraph_succ (n : ℕ) (f : ℕ → ZFSet.{u}) :
    finiteGraph (n+1) f = insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i,hi,he⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · exact Or.inr ⟨i,hi,he⟩
    · exact Or.inl he
  · rintro (he|⟨i,hi,he⟩)
    · exact ⟨n,Nat.lt_succ_self n,he⟩
    · exact ⟨i,Nat.lt_succ_of_lt hi,he⟩

theorem finiteGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (n : ℕ) (f : ℕ → ZFSet.{u}) (hf : ∀ i < n, f i ∈ M) : finiteGraph n f ∈ M := by
  induction n with
  | zero =>
    rw [finiteGraph_zero]
    exact hM _ hω _ ZFSet.omega_zero
  | succ n ih =>
    rw [finiteGraph_succ]
    have hn := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
    have hp := orderedPair_mem M hM hP hn (hf n (Nat.lt_succ_self n))
    have hs := singleton_mem M hM hP hp
    have hu := binary_union_mem M hM hP hU hs (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)))
    have he : ({ZFSet.pair (natSet n) (f n)} : ZFSet.{u}) ∪ finiteGraph n f =
        insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
    exact he ▸ hu

theorem eval_traceFormula (n x y p v g w z : ℕ) (e : ℕ → ZFSet.{u})
    (k : ℕ) (hn : e n = natSet k) (hw : e w = ZFSet.omega) (hz : e z = natSet 0) :
    (traceFormula n x y p v g w z).Eval e ↔ Trace (e v) (e g) k (e x) (e y) (e p) := by
  simp only [traceFormula,Formula.Eval,Formula.eval_pairMem,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_successor,cons_zero,cons_succ,hn,hw,hz,Trace]
  apply and_congr Iff.rfl
  apply and_congr _ Iff.rfl
  constructor
  · intro h i hi a ha hp
    obtain ⟨s,_,hs,b,hb,hpb,hgb⟩ := h (natSet i) ((natSet_mem_natSet i k).mpr hi) a ha hp
    exact ⟨b,hb,by simpa only [hs,natSet] using hpb,hgb⟩
  · intro h i hi a ha hp
    obtain ⟨j,hj,rfl⟩ := (mem_natSet k i).mp hi
    obtain ⟨b,hb,hpb,hgb⟩ := h j hj a ha hp
    exact ⟨natSet (j+1),(mem_omega _).mpr ⟨j+1,rfl⟩,rfl,b,hb,hpb,hgb⟩

theorem iterate_mem {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) : F^[n] x ∈ v := by
  induction n with
  | zero => exact hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

theorem trace_correct {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {n : ℕ} {x y p : ZFSet.{u}} (hx : x ∈ v) (ht : Trace v g n x y p) : y = F^[n] x := by
  have hp (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (F^[i] x) ∈ p := by
    induction i with
    | zero => exact ht.1
    | succ i ih =>
      have hv := iterate_mem F hF hx i
      obtain ⟨b,hb,hpb,hgb⟩ := ht.2.1 i (by omega) _ hv (ih (by omega))
      have he := (hg _ hv b hb).mp hgb
      simpa only [he,Function.iterate_succ_apply'] using hpb
  exact (ht.2.2 _ (iterate_mem F hF hx n) (hp n le_rfl)).symm

theorem finiteGraph_trace {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) :
    Trace v g n x (F^[n] x) (finiteGraph (n+1) (fun i => F^[i] x)) := by
  refine ⟨(pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_,?_⟩
  · intro i hi a ha hpa
    have he := ((pair_mem_finiteGraph _ _ _ _).mp hpa).2
    subst a
    refine ⟨F^[i+1] x,iterate_mem F hF hx (i+1),
      (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_⟩
    apply (hg _ (iterate_mem F hF hx i) _ (iterate_mem F hF hx (i+1))).mpr
    exact Function.iterate_succ_apply' F i x
  · intro b _ hpb
    exact ((pair_mem_finiteGraph _ _ _ _).mp hpb).2

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem mem_iterationSet {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) (z : ZFSet.{u}) :
    z ∈ iterationSet v F ↔ ∃ n : ℕ, ∃ x ∈ v,
      z = ZFSet.pair (ZFSet.pair (natSet n) x) (F^[n] x) := by
  rw [iterationSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨n,x,hx,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩,iterate_mem F hF hx n⟩,⟨n,x,hx,rfl⟩⟩

theorem eval_iterationFormula (z v g p d : ZFSet.{u}) :
    iterationFormula.Eval (cons z (cons ZFSet.omega (cons v (cons g
      (cons p (cons (natSet 0) (fun _ => d))))))) ↔
    ∃ n : ℕ, ∃ x ∈ v, ∃ y ∈ v, ∃ t ∈ d, ∃ s ∈ p,
      z = ZFSet.pair t y ∧ t = ZFSet.pair (natSet n) x ∧ Trace v g n x y s := by
  simp only [iterationFormula,Formula.Eval,cons_zero,cons_succ]
  rw [omega_exists]
  apply exists_congr
  intro n
  apply exists_congr
  intro x
  apply and_congr Iff.rfl
  apply exists_congr
  intro y
  apply and_congr Iff.rfl
  apply exists_congr
  intro t
  apply and_congr Iff.rfl
  apply exists_congr
  intro s
  apply and_congr Iff.rfl
  simp only [Formula.eval_orderedPair,cons_zero,cons_succ]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact eval_traceFormula _ _ _ _ _ _ _ _ _ n rfl rfl rfl

theorem iterationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {v g : ZFSet.{u}} (hv : v ∈ M) (hgM : g ∈ M)
    (F : ZFSet.{u} → ZFSet.{u}) (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x) :
    iterationSet v F ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  let d := ZFSet.prod ZFSet.omega v
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hv
  obtain ⟨p,hp,hpdef⟩ := internal_power M hM hPow hd
  have hprod := product_mem M hM hP hU hPow hS hd hv
  let e := cons ZFSet.omega (cons v (cons g (cons p (cons (natSet 0) (fun _ => d)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hv
    · exact hgM
    · exact hp
    · exact h0
    · exact hd
  have hs := sep_mem M hM hS iterationFormula e he hprod
  have eq : ZFSet.sep (fun z => iterationFormula.Eval (cons z e)) (ZFSet.prod d v) =
      iterationSet v F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_iterationSet F hF,
      show iterationFormula.Eval (cons z e) ↔ _ from eval_iterationFormula z v g p d]
    constructor
    · rintro ⟨_,n,x,hx,y,hy,t,ht,s,hs,hz,htx,htrace⟩
      exact ⟨n,x,hx,by rw [hz,htx,trace_correct F hF hg hx htrace]⟩
    · rintro ⟨n,x,hx,rfl⟩
      let s := finiteGraph (n+1) (fun i => F^[i] x)
      have hsM : s ∈ M := finiteGraph_mem M hM hP hU hω _ _
        (fun i _ => hM v hv _ (iterate_mem F hF hx i))
      have hsD : s ⊆ d := by
        intro z hz
        obtain ⟨i,hi,rfl⟩ := (mem_finiteGraph _ _ _).mp hz
        exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨i,rfl⟩,iterate_mem F hF hx i⟩
      have hsP := (hpdef s).mpr ⟨hsM,hsD⟩
      have htD : ZFSet.pair (natSet n) x ∈ d :=
        ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨htD,iterate_mem F hF hx n⟩,
        n,x,hx,_,iterate_mem F hF hx n,_,htD,s,hsP,rfl,rfl,?_⟩
      exact finiteGraph_trace F hF hg hx n
  exact eq ▸ hs

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem setSucc_nat (n : ℕ) : setSucc (natSet.{u} n) = natSet (n+1) := rfl

theorem setSucc_omega : ∀ x ∈ ZFSet.omega.{u}, setSucc x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨n+1,rfl⟩

theorem pair_mem_successorSet {x y : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hy : y ∈ ZFSet.omega) :
    ZFSet.pair x y ∈ successorSet ↔ y = setSucc x := by
  simp only [successorSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem successorSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : successorSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hprod := product_mem M hM hP hU hPow hS hω hω
  have hs := sep_mem M hM hS successorFormula (fun _ => ZFSet.omega) (fun _ => hω) hprod
  have eq : ZFSet.sep (fun z => successorFormula.Eval (cons z (fun _ => ZFSet.omega)))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = successorSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,successorFormula,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_successor,cons_zero,cons_succ,successorSet]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨x,hx,y,hy,hz,rfl⟩
      exact ⟨x,hx,hz⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,setSucc x,setSucc_omega x hx,rfl,rfl⟩
  exact eq ▸ hs

theorem iterate_setSucc (n m : ℕ) : setSucc^[n] (natSet.{u} m) = natSet (m+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change natSet (m+n+1) = natSet (m+(n+1))
    rw [Nat.add_assoc]

theorem addition_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ additionSet ↔ k = n+m := by
  rw [additionSet,mem_iterationSet setSucc setSucc_omega]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hinput,hout⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hi,rfl⟩ := ZFSet.pair_inj.mp hinput
    have hin := natSet_injective hi
    rw [←hin,iterate_setSucc] at hout
    exact (natSet_injective hout).trans (Nat.add_comm m n)
  · intro hk
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_setSucc,hk,Nat.add_comm m n]

theorem additionSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : additionSet.{u} ∈ M :=
  iterationSet_mem M hM hP hU hPow hS hI (omega_mem M hM hS hI)
    (successorSet_mem M hM hP hU hPow hS hI) setSucc setSucc_omega
    (fun _ hx _ hy => pair_mem_successorSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplicationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem numberPair_injective : Function.Injective numberPair.{u} := by
  intro a b h
  obtain ⟨hl,hr⟩ := ZFSet.pair_inj.mp h
  exact Prod.ext (natSet_injective hl) (natSet_injective hr)

theorem mem_pairNumbers (x : ZFSet.{u}) : x ∈ pairNumbers ↔ ∃ q, x = numberPair q := by
  constructor
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    exact ⟨(n,m),rfl⟩
  · rintro ⟨q,rfl⟩
    exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨q.1,rfl⟩,(mem_omega _).mpr ⟨q.2,rfl⟩⟩

@[simp] theorem addStep_numberPair (n m : ℕ) :
    addStep (numberPair.{u} (n,m)) = numberPair (n,n+m) := by
  have h := Function.leftInverse_invFun numberPair_injective (n,m)
  change Function.invFun numberPair.{u} (numberPair (n,m)) = (n,m) at h
  simp only [addStep,h]

theorem addStep_closed : ∀ x ∈ pairNumbers.{u}, addStep x ∈ pairNumbers := by
  intro x hx
  obtain ⟨⟨n,m⟩,rfl⟩ := (mem_pairNumbers x).mp hx
  rw [addStep_numberPair]
  exact (mem_pairNumbers _).mpr ⟨(n,n+m),rfl⟩

theorem pair_mem_addStepSet {x y : ZFSet.{u}} (hx : x ∈ pairNumbers) (hy : y ∈ pairNumbers) :
    ZFSet.pair x y ∈ addStepSet ↔ y = addStep x := by
  simp only [addStepSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem eval_addStepFormula (z : ZFSet.{u}) :
    addStepFormula.Eval (cons z (cons ZFSet.omega (cons pairNumbers (fun _ => additionSet)))) ↔
      ∃ x ∈ pairNumbers, z = ZFSet.pair x (addStep x) := by
  simp only [addStepFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨n,hn,m,hm,k,hk,x,hx,y,hy,hz,hxnm,hynk,hadd⟩
    obtain ⟨i,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨j,rfl⟩ := (mem_omega m).mp hm
    obtain ⟨l,rfl⟩ := (mem_omega k).mp hk
    rw [hxnm] at hadd
    have hl := (addition_code i j l).mp hadd
    refine ⟨x,hx,?_⟩
    rw [hz,hxnm,hynk,hl]
    exact congrArg (ZFSet.pair (numberPair (i,j))) (addStep_numberPair i j).symm
  · rintro ⟨x,hx,hz⟩
    obtain ⟨⟨i,j⟩,rfl⟩ := (mem_pairNumbers x).mp hx
    have hy : numberPair.{u} (i,i+j) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,natSet j,(mem_omega _).mpr ⟨j,rfl⟩,
      natSet (i+j),(mem_omega _).mpr ⟨i+j,rfl⟩,numberPair (i,j),hx,numberPair (i,i+j),hy,
      ?_,rfl,rfl,(addition_code i j (i+j)).mpr rfl⟩
    simpa only [addStep_numberPair] using hz

theorem addStepSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : addStepSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hp : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hp hp
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => additionSet))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i <;> simp [e,hω,hp,ha]
  have hs := sep_mem M hM hS addStepFormula e he hprod
  have eq : ZFSet.sep (fun z => addStepFormula.Eval (cons z e)) (ZFSet.prod pairNumbers pairNumbers) =
      addStepSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,show ∀ z, addStepFormula.Eval (cons z e) ↔ _ from eval_addStepFormula,
      addStepSet]
  exact eq ▸ hs

theorem iterate_addStep (n m : ℕ) :
    addStep^[n] (numberPair.{u} (m,0)) = numberPair (m,n*m) := by
  induction n with
  | zero => simp only [Function.iterate_zero,Function.id_def,Nat.zero_mul]
  | succ n ih => rw [Function.iterate_succ_apply',ih,addStep_numberPair,Nat.succ_mul,Nat.add_comm]

theorem multiplicationIteration_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : multiplicationIteration.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  exact iterationSet_mem M hM hP hU hPow hS hI
    (product_mem M hM hP hU hPow hS hω hω)
    (addStepSet_mem M hM hP hU hPow hS hI) addStep addStep_closed
    (fun _ hx _ hy => pair_mem_addStepSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem eval_mulFormula (n m k i d D z : ℕ) (e : ℕ → ZFSet.{u}) (a b c : ℕ)
    (hn : e n = natSet a) (hm : e m = natSet b) (hk : e k = natSet c)
    (hi : e i = multiplicationIteration) (hd : e d = pairNumbers)
    (hD : e D = ZFSet.prod ZFSet.omega pairNumbers) (hz : e z = natSet 0) :
    (mulFormula n m k i d D z).Eval e ↔ c = a*b := by
  simp only [mulFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,hn,hm,hk,hi,hd,hD,hz]
  constructor
  · rintro ⟨s,hs,t,ht,w,hw,hsb,htbc,hwas,hwt⟩
    change ZFSet.pair w t ∈ iterationSet pairNumbers addStep at hwt
    obtain ⟨q,x,hx,he⟩ := (mem_iterationSet addStep addStep_closed _).mp hwt
    obtain ⟨hleft,hright⟩ := ZFSet.pair_inj.mp he
    rw [hwas] at hleft
    obtain ⟨hqa,hxs⟩ := ZFSet.pair_inj.mp hleft
    have hq := natSet_injective hqa
    rw [←hxs,hsb,←hq] at hright
    change t = addStep^[a] (numberPair (b,0)) at hright
    rw [iterate_addStep,htbc] at hright
    exact natSet_injective (ZFSet.pair_inj.mp hright).2
  · intro hc
    have hs : numberPair.{u} (b,0) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    have ht : numberPair.{u} (b,c) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    have hw : ZFSet.pair (natSet a) (numberPair.{u} (b,0)) ∈ ZFSet.prod ZFSet.omega pairNumbers :=
      ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨a,rfl⟩,hs⟩
    refine ⟨numberPair (b,0),hs,numberPair (b,c),ht,_,hw,rfl,rfl,rfl,?_⟩
    exact (mem_iterationSet addStep addStep_closed _).mpr
      ⟨a,numberPair (b,0),hs,by rw [iterate_addStep,hc]⟩

theorem multiplication_code (n m k : ℕ) :
    ZFSet.pair (numberPair.{u} (n,m)) (natSet k) ∈ multiplicationSet ↔ k = n*m := by
  simp only [multiplicationSet,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨_,a,b,he⟩
    obtain ⟨hin,hout⟩ := ZFSet.pair_inj.mp he
    have hab := numberPair_injective hin
    have hn : n = a := congrArg Prod.fst hab
    have hm : m = b := congrArg Prod.snd hab
    simpa only [←hn,←hm] using natSet_injective hout
  · intro hk
    exact ⟨⟨(mem_pairNumbers _).mpr ⟨_,rfl⟩,(mem_omega _).mpr ⟨k,rfl⟩⟩,
      n,m,by rw [hk]⟩

theorem multiplicationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : multiplicationSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have hD := product_mem M hM hP hU hPow hS hω hd
  have hi := multiplicationIteration_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hd hω
  let e := cons ZFSet.omega (cons pairNumbers (cons multiplicationIteration
    (cons (ZFSet.prod ZFSet.omega pairNumbers) (fun _ => natSet 0))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hd
    · exact hi
    · exact hD
    · exact h0
  have hs := sep_mem M hM hS multiplicationFormula e he hprod
  have hφ (z : ZFSet.{u}) : multiplicationFormula.Eval (cons z e) ↔
      ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (n*m)) := by
    simp only [multiplicationFormula,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,m,hm,k,hk,t,ht,hz,htnm,hmu⟩
      obtain ⟨a,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨b,rfl⟩ := (mem_omega m).mp hm
      obtain ⟨c,rfl⟩ := (mem_omega k).mp hk
      have hc := (eval_mulFormula 3 2 1 7 6 8 9
        (cons t (cons (natSet c) (cons (natSet b) (cons (natSet a) (cons z e)))))
        a b c rfl rfl rfl rfl rfl rfl rfl).mp hmu
      exact ⟨a,b,by simpa only [htnm,hc,numberPair] using hz⟩
    · rintro ⟨n,m,rfl⟩
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,
        natSet (n*m),(mem_omega _).mpr ⟨n*m,rfl⟩,numberPair (n,m),
        (mem_pairNumbers _).mpr ⟨_,rfl⟩,rfl,rfl,?_⟩
      exact (eval_mulFormula 3 2 1 7 6 8 9
        (cons (numberPair (n,m)) (cons (natSet (n*m)) (cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (numberPair (n,m)) (natSet (n*m))) e)))))
        n m (n*m) rfl rfl rfl rfl rfl rfl rfl).mpr rfl
  have eq : ZFSet.sep (fun z => multiplicationFormula.Eval (cons z e))
      (ZFSet.prod pairNumbers ZFSet.omega) = multiplicationSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,hφ,multiplicationSet]
  exact eq ▸ hs

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelSequences
universe u
noncomputable section

@[simp] theorem natPair_mem (n m : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet m) ∈ pairNumbers :=
  (mem_pairNumbers _).mpr ⟨(n,m),rfl⟩

theorem multiplication_code' (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ multiplicationSet ↔ k = n*m :=
  multiplication_code n m k

theorem eval_pairFormula (n m k a b d w : ℕ) (e : ℕ → ZFSet.{u}) (i j l : ℕ)
    (hn : e n = natSet i) (hm : e m = natSet j) (hk : e k = natSet l)
    (ha : e a = additionSet) (hb : e b = multiplicationSet)
    (hd : e d = pairNumbers) (hw : e w = ZFSet.omega) :
    (pairFormula n m k a b d w).Eval e ↔ l = Nat.pair i j := by
  simp only [pairFormula,Formula.eval_disj,Formula.Eval,eval_tripleFormula,
    cons_zero,cons_succ,hn,hm,hk,ha,hb,hd,hw,natSet_mem_natSet]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,addition_code,multiplication_code']
  by_cases h : i < j <;> simp [h,Nat.pair]

theorem pairingSet_code : PairingCode pairingSet.{u} := by
  intro n m k
  simp only [pairingSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,natPair_mem,true_and]
  constructor
  · rintro ⟨_,a,b,he⟩
    obtain ⟨hin,hout⟩ := ZFSet.pair_inj.mp he
    have hab : (n,m) = (a,b) := numberPair_injective hin
    have hn : n = a := congrArg Prod.fst hab
    have hm : m = b := congrArg Prod.snd hab
    simpa only [←hn,←hm] using natSet_injective hout
  · intro hk
    exact ⟨(mem_omega _).mpr ⟨k,rfl⟩,n,m,by simp only [hk,numberPair]⟩

theorem pairingSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : pairingSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  have hb := multiplicationSet_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hd hω
  let e := cons ZFSet.omega (cons pairNumbers (cons additionSet (fun _ => multiplicationSet)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hd
    · exact ha
    · exact hb
  have hs := sep_mem M hM hS pairingFormula e he hprod
  have hφ (z : ZFSet.{u}) : pairingFormula.Eval (cons z e) ↔
      ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m)) := by
    simp only [pairingFormula,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,m,hm,k,hk,t,ht,hz,htnm,hpr⟩
      obtain ⟨a,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨b,rfl⟩ := (mem_omega m).mp hm
      obtain ⟨c,rfl⟩ := (mem_omega k).mp hk
      have hc := (eval_pairFormula 3 2 1 7 8 6 5
        (cons t (cons (natSet c) (cons (natSet b) (cons (natSet a) (cons z e)))))
        a b c rfl rfl rfl rfl rfl rfl rfl).mp hpr
      exact ⟨a,b,by simpa only [htnm,hc,numberPair] using hz⟩
    · rintro ⟨n,m,rfl⟩
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,
        natSet (Nat.pair n m),(mem_omega _).mpr ⟨Nat.pair n m,rfl⟩,numberPair (n,m),
        natPair_mem n m,rfl,rfl,?_⟩
      exact (eval_pairFormula 3 2 1 7 8 6 5
        (cons (numberPair (n,m)) (cons (natSet (Nat.pair n m)) (cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m))) e)))))
        n m (Nat.pair n m) rfl rfl rfl rfl rfl rfl rfl).mpr rfl
  have eq : ZFSet.sep (fun z => pairingFormula.Eval (cons z e))
      (ZFSet.prod pairNumbers ZFSet.omega) = pairingSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,hφ,pairingSet]
  exact eq ▸ hs

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}} (C : Context M)
include C

theorem Context.omega_mem : ZFSet.omega.{u} ∈ M :=
  BoundedSetTheory.omega_mem M C.transitive C.separation C.infinity

theorem Context.nat_mem (n : ℕ) : natSet.{u} n ∈ M :=
  C.transitive _ C.omega_mem _ ((mem_omega _).mpr ⟨n,rfl⟩)

theorem Context.prod_mem {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ZFSet.prod a b ∈ M :=
  product_mem M C.transitive C.pairing C.union C.power C.separation ha hb

theorem graph_of_formula (f : ℕ → ℕ) (p : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M)
    (hp : ∀ n m, p.Eval (cons (ZFSet.pair (natSet n) (natSet m)) e) ↔ m = f n) :
    HasGraph M f := by
  refine ⟨ZFSet.sep (fun z => p.Eval (cons z e)) pairNumbers,
    sep_mem M C.transitive C.separation p e he (C.prod_mem C.omega_mem C.omega_mem),?_⟩
  intro n m
  simp only [ZFSet.mem_sep,natPair_mem,true_and,hp]

theorem graph_of_relation (f : ℕ → ℕ) (p : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M)
    (hp : ∀ n m, p.Eval (cons (natSet m) (cons (natSet n) e)) ↔ m = f n) :
    HasGraph M f := by
  let r : ℕ → ℕ := fun i => if i < 2 then i else i+2
  let q : Formula := .existsMem 1 (.existsMem 2
    (.conj (.orderedPair 2 1 0) (p.rename r)))
  let d := cons ZFSet.omega e
  apply graph_of_formula C f q d
  · intro i
    cases i with
    | zero => exact C.omega_mem
    | succ i => exact he i
  · intro n m
    simp only [q,d,Formula.Eval,Formula.eval_orderedPair,Formula.eval_rename_comp,
      cons_zero,cons_succ]
    constructor
    · rintro ⟨x,hx,y,hy,hz,hp'⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hz
      have hh : cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (natSet n) (natSet m)) (cons ZFSet.omega e))) ∘ r =
          cons (natSet m) (cons (natSet n) e) := by
        funext i
        rcases i with _|_|i <;> simp [r,cons]
      rw [hh] at hp'
      exact (hp n m).mp hp'
    · intro h
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,
        (mem_omega _).mpr ⟨m,rfl⟩,rfl,?_⟩
      have hh : cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (natSet n) (natSet m)) (cons ZFSet.omega e))) ∘ r =
          cons (natSet m) (cons (natSet n) e) := by
        funext i
        rcases i with _|_|i <;> simp [r,cons]
      rw [hh]
      exact (hp n m).mpr h

theorem const_graph (k : ℕ) : HasGraph M (fun _ => k) := by
  apply graph_of_relation C _ (.equal 0 2) (fun _ => natSet k) (fun _ => C.nat_mem k)
  intro n m
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem id_graph : HasGraph M id := by
  apply graph_of_relation C _ (.equal 0 1) (fun _ => ZFSet.omega) (fun _ => C.omega_mem)
  intro n m
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem succ_graph : HasGraph M Nat.succ := by
  refine ⟨successorSet,successorSet_mem M C.transitive C.pairing C.union C.power
    C.separation C.infinity,?_⟩
  intro n m
  rw [pair_mem_successorSet ((mem_omega _).mpr ⟨n,rfl⟩)
    ((mem_omega _).mpr ⟨m,rfl⟩),setSucc_nat]
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem HasGraph.comp {f g : ℕ → ℕ} (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (fun n => f (g n)) := by
  obtain ⟨a,ha,hac⟩ := hf
  obtain ⟨b,hb,hbc⟩ := hg
  let e := cons ZFSet.omega (cons a (fun _ => b))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,ha,hb]
  apply graph_of_relation C _ (.existsMem 2 (.conj (.pairMem 2 0 5) (.pairMem 0 1 4))) e he
  intro n m
  simp only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [hac,hbc]
  constructor
  · rintro ⟨k,rfl,h⟩
    exact h
  · intro h
    exact ⟨g n,rfl,h⟩

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}} (C : Context M)
include C

theorem Context.pairing_mem : pairingSet.{u} ∈ M :=
  pairingSet_mem M C.transitive C.pairing C.union C.power C.separation C.infinity

theorem Context.pairNumbers_mem : pairNumbers.{u} ∈ M := C.prod_mem C.omega_mem C.omega_mem

omit C in
@[simp] theorem pairing_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ pairingSet ↔
      k = Nat.pair n m := pairingSet_code n m k

theorem left_graph : HasGraph M (fun n => (Nat.unpair n).1) := by
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => pairingSet))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (tripleFormula 1 0 2 5 4)) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨k,rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair n).2,by rw [h,Nat.pair_unpair]⟩

theorem right_graph : HasGraph M (fun n => (Nat.unpair n).2) := by
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => pairingSet))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (tripleFormula 0 1 2 5 4)) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨k,rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair n).1,by rw [h,Nat.pair_unpair]⟩

theorem HasGraph.pair {f g : ℕ → ℕ} (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (fun n => Nat.pair (f n) (g n)) := by
  obtain ⟨a,ha,hac⟩ := hf
  obtain ⟨b,hb,hbc⟩ := hg
  let e := cons ZFSet.omega (cons a (cons b (cons pairNumbers (fun _ => pairingSet))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp [e,C.omega_mem,ha,hb,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (.existsMem 3
    (.conj (.pairMem 3 1 5) (.conj (.pairMem 3 0 6) (tripleFormula 1 0 2 8 7))))) e he
  intro n m
  simp only [Formula.Eval,Formula.eval_pairMem,eval_tripleFormula,cons_zero,cons_succ,e]
  simp_rw [omega_exists]
  simp only [hac,hbc,natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨i,j,rfl,rfl,h⟩
    exact h
  · intro h
    exact ⟨f n,g n,rfl,rfl,h⟩

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}} (C : Context M)
include C

omit C in
theorem natLift_closed (f : ℕ → ℕ) : ∀ x ∈ ZFSet.omega.{u}, natLift f x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨f n,natLift_nat f n⟩

omit C in
theorem iterate_natLift (f : ℕ → ℕ) (n m : ℕ) :
    (natLift f)^[n] (natSet.{u} m) = natSet (f^[n] m) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,natLift_nat,Function.iterate_succ_apply']

omit C in
theorem natIteration_code (f : ℕ → ℕ) (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ natIteration f ↔
      k = f^[n] m := by
  rw [natIteration,mem_iterationSet _ (natLift_closed f)]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hi,hk⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hnum,rfl⟩ := ZFSet.pair_inj.mp hi
    have hin := natSet_injective hnum
    rw [←hin,iterate_natLift] at hk
    exact natSet_injective hk
  · intro h
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_natLift,h]

theorem natIteration_mem {f : ℕ → ℕ} (hf : HasGraph M f) : natIteration.{u} f ∈ M := by
  obtain ⟨g,hg,hgc⟩ := hf
  apply iterationSet_mem M C.transitive C.pairing C.union C.power C.separation C.infinity
    C.omega_mem hg (natLift f) (natLift_closed f)
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
  rw [hgc,natLift_nat]
  exact ⟨fun h => congrArg natSet h,fun h => natSet_injective h⟩

theorem HasGraph.iterate {f : ℕ → ℕ} (hf : HasGraph M f) :
    HasGraph M (fun v => f^[(Nat.unpair v).2] (Nat.unpair v).1) := by
  let e := cons ZFSet.omega (cons pairNumbers (cons pairingSet (fun _ => natIteration f)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|i <;>
      simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem,natIteration_mem C hf]
  apply graph_of_relation C _ (.existsMem 2 (.existsMem 3 (.existsMem 5
    (.conj (tripleFormula 2 1 4 7 6)
      (.conj (.orderedPair 0 1 2) (.pairMem 0 3 8)))))) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨a,b,t,ht,hn,rfl,h⟩
    rw [natIteration_code] at h
    simpa only [hn,Nat.unpair_pair] using h
  · intro h
    refine ⟨(Nat.unpair n).1,(Nat.unpair n).2,
      ZFSet.pair (natSet (Nat.unpair n).2) (natSet (Nat.unpair n).1),
      natPair_mem _ _,(Nat.pair_unpair n).symm,rfl,?_⟩
    exact (natIteration_code _ _ _ _).mpr h

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPrimrec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem HasGraph.congr {f g : ℕ → ℕ} (hf : HasGraph M f) (h : ∀ n, f n = g n) :
    HasGraph M g := (funext h) ▸ hf

theorem iterate_recStep (f g : ℕ → ℕ) (z n : ℕ) :
    (recStep g)^[n] (recStart f z) = Nat.pair z (Nat.pair n (recValue f g z n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [recStep,Nat.unpair_pair,recValue]

theorem HasGraph.prec (C : Context M) {f g : ℕ → ℕ}
    (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (Nat.unpaired (recValue f g)) := by
  have hs : HasGraph M (recStep g) :=
    HasGraph.pair C (left_graph C) (HasGraph.pair C
      (HasGraph.comp C (succ_graph C) (HasGraph.comp C (left_graph C) (right_graph C))) hg)
  have hz : HasGraph M (recStart f) :=
    HasGraph.pair C (id_graph C) (HasGraph.pair C (const_graph C 0) hf)
  have hp := HasGraph.pair C (HasGraph.comp C hz (left_graph C)) (right_graph C)
  have hi := HasGraph.comp C (HasGraph.iterate C hs) hp
  have h := HasGraph.comp C (HasGraph.comp C (right_graph C) (right_graph C)) hi
  apply h.congr
  intro v
  simp only [Nat.unpair_pair,iterate_recStep,Nat.unpaired]

theorem natPrimrec_graph (C : Context M) {f : ℕ → ℕ} (hf : Nat.Primrec f) : HasGraph M f := by
  induction hf with
  | zero => exact const_graph C 0
  | succ => exact succ_graph C
  | left => exact left_graph C
  | right => exact right_graph C
  | pair hf hg ihf ihg => exact HasGraph.pair C ihf ihg
  | comp hf hg ihf ihg => exact HasGraph.comp C ihf ihg
  | prec hf hg ihf ihg => exact HasGraph.prec C ihf ihg

theorem primrec_graph (C : Context M) {f : ℕ → ℕ} (hf : Primrec f) : HasGraph M f :=
  natPrimrec_graph C (Primrec.nat_iff.mp hf)

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelArithmeticSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section

variable {M : ZFSet.{u}}

@[simp] theorem pairCode_nat (i j k : ℕ) :
    PairCode (natSet.{u} i) (natSet j) (natSet k) ↔ k = Nat.pair i j := by
  simp only [PairCode,natPair_mem,true_and,pairing_code]

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenWordCodeGraph
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic SetModelReals
open Encodable EncodedForcing

theorem wordBit_primrec : Primrec wordBit :=
  CommonIdeal.bit_primrec.comp ((Primrec.list_getD false).comp
    (word_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

theorem wordGraphFormula_spec (gl gb : ZFSet.{0})
    (hl : GraphCode gl (fun n => (word n).length)) (hb : GraphCode gb wordBit)
    (n : ℕ) (q : ZFSet.{0}) :
    wordGraphFormula.Eval (wordGraphEnv q (natSet n) gl gb) ↔
      q = wordCode (word n) := by
  simp only [wordGraphFormula,wordGraphEnv,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_functionGraph,Formula.eval_allMem,eval_tripleFormula,
    cons_zero,cons_succ]
  simp_rw [omega_exists]
  simp only [hl]
  constructor
  · rintro ⟨l,rfl,hq,hi⟩
    have hq' : FunctionGraph (natSet (word n).length) alphabet q := hq
    have hbits (i : ℕ) (h : i < (word n).length) :
        ZFSet.pair (natSet i) (bitSet (word n)[i]) ∈ q := by
      obtain ⟨k,b,⟨_,hk⟩,hb',hi'⟩ := hi (natSet i) ((natSet_mem_natSet _ _).mpr h)
      have hk' : k = Nat.pair n i := (pairing_code n i k).mp hk
      have hb'' := (hb k b).mp hb'
      subst k
      subst b
      simpa [wordBit,List.getD,h,bitSet] using hi'
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x,hx,y,_,rfl⟩ := hq'.1 z hz
      obtain ⟨i,hi,rfl⟩ := (mem_natSet _ _).mp hx
      have hy := hq'.functional ((natSet_mem_natSet _ _).mpr hi) hz (hbits i hi)
      rw [hy]
      exact (mem_wordCode _ _).mpr ⟨⟨i,hi⟩,rfl⟩
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_wordCode _ _).mp hz
      exact hbits i.val i.isLt
  · rintro rfl
    refine ⟨(word n).length,rfl,wordCode_function _,?_⟩
    intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet _ _).mp hx
    refine ⟨Nat.pair n i,wordBit (Nat.pair n i),⟨natPair_mem _ _,
      (pairing_code _ _ _).mpr rfl⟩,(hb _ _).mpr rfl,?_⟩
    simp only [wordBit,Nat.unpair_pair]
    exact (pair_mem_wordCode _ _ _).mpr ⟨hi,by simp [List.getD,hi]⟩

theorem mem_wordCodeGraph (z : ZFSet.{0}) : z ∈ wordCodeGraph ↔
    ∃ n : ℕ, z = ZFSet.pair (natSet n) (wordCode (word n)) := by
  simp only [wordCodeGraph,ZFSet.mem_range,eq_comm]

theorem pair_mem_wordCodeGraph (n : ℕ) (q : ZFSet.{0}) :
    ZFSet.pair (natSet n) q ∈ wordCodeGraph ↔ q = wordCode (word n) := by
  rw [mem_wordCodeGraph]
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨hn,hq⟩ := ZFSet.pair_inj.mp hk
    have hn' := natSet_injective hn
    simpa only [← hn'] using hq
  · intro h
    exact ⟨n,by rw [h]⟩

theorem wordCodeGraph_function : FunctionGraph ZFSet.omega conditions wordCodeGraph := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_wordCodeGraph z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,wordCode (word n),
      (mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨wordCode (word n),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
      (pair_mem_wordCodeGraph _ _).mpr rfl,
      fun y _ hy => (pair_mem_wordCodeGraph n y).mp hy⟩

theorem wordCodeGraph_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    wordCodeGraph ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨gl,hgl,hl⟩ := primrec_graph C (Primrec.list_length.comp word_primrec)
  obtain ⟨gb,hgb,hb⟩ := primrec_graph C wordBit_primrec
  let r : ℕ → ℕ := fun i => if i < 2 then i else i+3
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (wordGraphFormula.rename r)))
  let e := cons ZFSet.omega (cons conditions (cons gl (cons gb
    (cons ZFSet.omega (cons alphabet (cons pairNumbers (fun _ => pairingSet)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|i
    · exact C.omega_mem
    · exact conditions_mem M hM hT
    · exact hgl
    · exact hgb
    · exact C.omega_mem
    · exact alphabet_mem M hM hT
    · exact C.pairNumbers_mem
    · exact C.pairing_mem
  have hs := sep_mem M hM C.separation φ e he
    (C.prod_mem C.omega_mem (conditions_mem M hM hT))
  have hspec (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ wordCodeGraph := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_rename_comp,
      cons_zero,cons_succ,e]
    rw [omega_exists,mem_wordCodeGraph]
    have hh (n : ℕ) (q : ZFSet.{0}) :
        cons q (cons (natSet n) (cons z e)) ∘ r = wordGraphEnv q (natSet n) gl gb := by
      funext i
      rcases i with _|_|i <;> simp [r,e,wordGraphEnv,cons]
    simp_rw [show ∀ n q, (cons q (cons (natSet n) (cons z
      (cons ZFSet.omega (cons conditions (cons gl (cons gb (cons ZFSet.omega
      (cons alphabet (cons pairNumbers (fun _ => pairingSet))))))))))) ∘ r =
      wordGraphEnv q (natSet n) gl gb from hh]
    simp_rw [wordGraphFormula_spec gl gb hl hb]
    constructor
    · rintro ⟨n,q,_,hz,rfl⟩
      exact ⟨n,hz⟩
    · rintro ⟨n,rfl⟩
      exact ⟨n,wordCode (word n),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl,rfl⟩
  have heq : ZFSet.sep (fun z => φ.Eval (cons z e))
      (ZFSet.prod ZFSet.omega conditions) = wordCodeGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,hspec]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr (wordCodeGraph_function.1 z hz),hz⟩⟩
  exact heq ▸ hs

theorem canonical_wordCodeGraph (p : List Bool) (q : ZFSet.{0}) :
    ZFSet.pair (natSet (encode p)) q ∈ wordCodeGraph ↔ q = wordCode p := by
  simp only [pair_mem_wordCodeGraph,word,encodek,Option.getD_some]

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFilters
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem filter_ext {P : Type*} [Preorder P] (F H : GenericFilter P)
    (h : F.carrier = H.carrier) : F = H := by
  cases F; cases H; cases h; rfl

theorem pull_push (G : GenericFilter Condition) : pullFilter (pushFilter G) = G := by
  have he : (pullFilter (pushFilter G)).carrier = G.carrier := by
    ext p; simp [pullFilter,pushFilter]
  exact filter_ext _ _ he

theorem dense_pull_iff (D : Set (Conditions conditions)) :
    Dense {p : Condition | conditionEquiv p ∈ D} ↔ Dense D := by
  constructor
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv.symm q)
    exact ⟨conditionEquiv p,by simpa using conditionEquiv.monotone hp,hpD⟩
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv q)
    exact ⟨conditionEquiv.symm p,by simpa using conditionEquiv.symm.monotone hp,
      by simpa using hpD⟩

theorem groundGeneric_iff (M : ZFSet.{0}) (G : GenericFilter (Conditions conditions)) :
    AtomicForcing.GroundGeneric M G ↔
      ∀ D ∈ M, Dense {p : Condition | wordCode p.word ∈ D} →
        ∃ p ∈ (pullFilter G).carrier, wordCode p.word ∈ D := by
  have hl (p : Condition) : label conditions (conditionEquiv p) = wordCode p.word :=
    label_encodeCondition p
  constructor
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mp (by simpa only [Set.mem_ofPred_eq,hl] using hd)
    obtain ⟨q,hq,hqD⟩ := h D hD hd'
    refine ⟨conditionEquiv.symm q,by simpa [pullFilter] using hq,?_⟩
    simpa only [←hl,OrderIso.apply_symm_apply] using hqD
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mpr hd
    obtain ⟨q,hq,hqD⟩ := h D hD (by simpa only [Set.mem_ofPred_eq,hl] using hd')
    exact ⟨conditionEquiv q,hq,by simpa only [hl] using hqD⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffleCertificate
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteShuffleCertificate
open FiniteShuffle ShuffleRequirements GenericCoding

theorem certificate_transfer (D : List Bool → Prop) (q : List Bool)
    (h : Certificate D q) : Transfer D q := by
  obtain ⟨k,hk,hs⟩ := h
  intro A
  obtain ⟨l,hl,hD⟩ := hs (initial A k) (prefix_length A k)
  refine ⟨_,hD,fun G hG => ?_⟩
  apply (realizes_initial _ _ _).mpr
  apply code_agree
  · intro i hi
    exact prefix_getD A k i (lt_of_lt_of_le hi hl)
  · exact hG.mono (by omega)

theorem certificate_mono (D : List Bool → Prop) {q r : List Bool}
    (hqr : q <+: r) (h : Certificate D q) : Certificate D r := by
  obtain ⟨k,hk,hs⟩ := h
  refine ⟨k,hk.trans hqr.length_le,fun s hsk => ?_⟩
  obtain ⟨l,hl,hD⟩ := hs s hsk
  refine ⟨l,hl,?_⟩
  have he : Agree l (code (fun i => s.getD i false) (fun i => q.getD i false))
      (code (fun i => s.getD i false) (fun i => r.getD i false)) :=
    code_agree (fun _ _ => rfl) (fun i hi => getD_of_prefix hqr i (by omega))
  rwa [←prefix_agree he]

theorem certificate_denseOpen (D : List Bool → Prop) (hD : DenseOpen D) :
    DenseOpen (Certificate D) := by
  refine ⟨?_,fun _ _ hqr h => certificate_mono D hqr h⟩
  intro p
  let G : Oracle := fun i => p.getD i false
  obtain ⟨m,H,hn,hGH,_,hall⟩ := all_extension D hD (p.length+1) G
  let q := initial H (2*m)
  refine ⟨q,?_,m,by simp [q],fun s _ => ?_⟩
  · rw [←prefix_default p]
    exact initial_prefix (by omega) (hGH.mono (by omega))
  · obtain ⟨l,hl,hDl⟩ := hall (fun i => s.getD i false)
    refine ⟨l,hl,?_⟩
    have he : Agree l (code (fun i => s.getD i false) (fun i => q.getD i false))
        (code (fun i => s.getD i false) H) :=
      code_agree (fun _ _ => rfl) (fun i hi => prefix_getD H (2*m) i (by omega))
    rwa [prefix_agree he]

end TuringRigidity.FiniteShuffleCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffleComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteShuffleComputation
open Encodable EncodedForcing GenericCoding FiniteShuffle UniformOracle BinarySeries

theorem wordCount_primrec :
    Primrec₂ (fun (p : List Bool) n => count (fun i => p.getD i false) n) := by
  have hs : Primrec (fun z : List Bool × ℕ × ℕ =>
      z.2.2 + if z.1.getD (2*z.2.1+1) false then 1 else 0) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp Primrec.fst
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.fst.comp Primrec.snd)))) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))
  exact (Primrec.nat_rec (Primrec.const 0) hs.to₂).of_eq (fun p n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      change _ + _ = count (fun i => p.getD i false) n + bit (fun i => p.getD i false) (2*n+1)
      rw [ih]
      rfl)

theorem wordShuffleBit_primrec :
    Primrec (fun z : List Bool × List Bool × ℕ =>
      code (fun i => z.1.getD i false) (fun i => z.2.1.getD i false) z.2.2) := by
  let hp : Primrec (fun z : List Bool × List Bool × ℕ => z.2.1) :=
    Primrec.fst.comp Primrec.snd
  let hn : Primrec (fun z : List Bool × List Bool × ℕ => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hc := wordCount_primrec.comp hp hn
  exact Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp hp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hn))) (Primrec.const true))
    ((Primrec.list_getD false).comp Primrec.fst hc)
    ((Primrec.list_getD false).comp hp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp hn hc)))

theorem finiteShuffleWord_primrec :
    Primrec (fun z : ℕ => finiteShuffleWord (Nat.unpair z).1
      (Nat.unpair (Nat.unpair z).2).1 (Nat.unpair (Nat.unpair z).2).2) := by
  let hu := Primrec.fst.comp Primrec.unpair
  let hv := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  let hl := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hl)
    (wordShuffleBit_primrec.comp ((word_primrec.comp (hu.comp Primrec.fst)).pair
      ((word_primrec.comp (hv.comp Primrec.fst)).pair Primrec.snd))).to₂)

end TuringRigidity.FiniteShuffleComputation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticShuffleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticShuffleCertificate
open Encodable UniformArithmetic FiniteShuffleComputation FiniteShuffleCertificate
open EncodedForcing (word word_primrec)

theorem certificate_arith :
    Arith (fun O n => Certificate (fun t => O 0 (encode t) = true) (word n)) := by
  let L := left_primrec
  let R := right_primrec

  let hn := L.comp (L.comp L)
  let hk := R.comp (L.comp L)
  let hs := R.comp L
  have hshuffle := finiteShuffleWord_primrec.comp
    (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp hn R))
  have hquery := (Arith.query 0).comp _ hshuffle
  have hbound := Arith.pure (fun v => right v ≤ right (left (left v)))
    (Primrec.nat_le.comp R hk)
  have hex := (hbound.and hquery).ex
  have hlength := equal (Primrec.list_length.comp (word_primrec.comp R)) (R.comp L)
  have hall := (hlength.imp hex).all
  have hsize := Arith.pure (fun v => 2 * right v ≤ (word (left v)).length)
    (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.const 2) R)
      (Primrec.list_length.comp (word_primrec.comp L)))
  apply (hsize.and hall).ex.congr
  intro O n
  simp only [left,right,Nat.unpair_pair,finiteShuffleWord]
  constructor
  · rintro ⟨k,hk,h⟩
    refine ⟨k,hk,fun s hs => ?_⟩
    have hlen : (word (encode s)).length = k := by simpa [word] using hs
    simpa [word] using h (encode s) hlen
  · rintro ⟨k,hk,h⟩
    exact ⟨k,hk,fun s hs => h (word s) hs⟩

theorem open_arith : Arith (fun O n =>
    ∃ r : List Bool, O 0 (encode r) = true ∧ r <+: word n) := by
  have hp : Arith (fun (_ : Oracles) v => word (right v) <+: word (left v)) :=
    (Arith.pure _ (Primrec.eq.comp (word_primrec.comp right_primrec)
      (Primrec.list_take.comp (Primrec.list_length.comp (word_primrec.comp right_primrec))
        (word_primrec.comp left_primrec)))).congr (fun _ _ => List.prefix_iff_eq_take.symm)
  have hq := (Arith.query 0).comp _ (Primrec.encode.comp (word_primrec.comp right_primrec))
  apply (hq.and hp).ex.congr
  intro O n
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨r,hr,hp⟩
    exact ⟨word r,hr,hp⟩
  · rintro ⟨r,hr,hp⟩
    exact ⟨encode r,by simpa [word] using hr,by simpa [word] using hp⟩

end TuringRigidity.ArithmeticShuffleCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalCohenSets
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable

theorem wordPullback_true (D : ZFSet.{0}) (n : ℕ) :
    wordPullback D n = true ↔ wordCode (EncodedForcing.word n) ∈ D := by
  classical
  simp [wordPullback]

theorem wordPullback_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : realCode (wordPullback D) ∈ M := by
  let e := cons D (fun _ => wordCodeGraph)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hD
    | succ i => exact wordCodeGraph_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 1 0 3)) e he (sourceT_omega_mem M hM hT)
  have heq : ZFSet.sep (fun n =>
      (Formula.existsMem 1 (.pairMem 1 0 3)).Eval (cons n e)) ZFSet.omega =
      realCode (wordPullback D) := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨hx,q,hq,hxq⟩
      obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [(pair_mem_wordCodeGraph n q).mp hxq] at hq
      exact (natSet_mem_realCode _ _).mpr ((wordPullback_true D n).mpr hq)
    · intro hx
      obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
      exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,wordCode (EncodedForcing.word n),
        (wordPullback_true D n).mp ((natSet_mem_realCode _ _).mp hx),
        (pair_mem_wordCodeGraph _ _).mpr rfl⟩
  exact heq ▸ hh

theorem wordImage_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : realCode A ∈ M) : wordImage A ∈ M := by
  let e := cons (realCode A) (fun _ => wordCodeGraph)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hA
    | succ i => exact wordCodeGraph_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) e he (conditions_mem M hM hT)
  simpa only [wordImage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using hh

theorem wordImage_spec (P : List Bool → Prop) (A : Oracle)
    (hA : ∀ n, A n = true ↔ P (EncodedForcing.word n)) (p : List Bool) :
    wordCode p ∈ wordImage A ↔ P p := by
  rw [wordImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,hq⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
    have hp := wordCode_injective ((pair_mem_wordCodeGraph _ _).mp hq)
    rw [hp]
    exact (hA n).mp ((natSet_mem_realCode _ _).mp hx)
  · intro hp
    exact ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,natSet (encode p),
      (natSet_mem_realCode _ _).mpr ((hA _).mpr (by simpa [EncodedForcing.word] using hp)),
      (canonical_wordCodeGraph p _).mpr rfl⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeRecovery InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_properties (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let N := genericExtensionSet M c G.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ genericFilterSet c G.carrier ∈ N := by
  let _ : Top (Conditions c) := ⟨Classical.choose G.nonempty⟩
  have ht : ⊤ ∈ G.carrier := Classical.choose_spec G.nonempty
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
      (InternalCollapse.orderSet_pair c) G hG ht,
    ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht,
    genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht⟩

end TuringRigidity.RegularTreeExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalShuffleSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable UniformArithmetic
open FiniteShuffleCertificate FiniteShuffle CohenBorelForcing CountableForcing

theorem shuffleOpenCodes_true (D : ZFSet.{0}) (n : ℕ) :
    shuffleOpenCodes D n = true ↔ shuffleOpen D (EncodedForcing.word n) := by
  rw [shuffleOpenCodes,arithmeticReal_true]
  simp only [wordPullback_true,EncodedForcing.word,encodek,Option.getD_some,shuffleOpen]

theorem shuffleOpenCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : realCode (shuffleOpenCodes D) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT ArithmeticShuffleCertificate.open_arith
    (fun _ => wordPullback D) (fun _ => wordPullback_mem M hM hT D hD)

theorem shuffleCertificateCodes_true (D : ZFSet.{0}) (n : ℕ) :
    shuffleCertificateCodes D n = true ↔ Certificate (shuffleOpen D) (EncodedForcing.word n) := by
  rw [shuffleCertificateCodes,arithmeticReal_true]
  simp only [Certificate,shuffleOpenCodes_true,EncodedForcing.word,encodek,Option.getD_some]

theorem shuffleCertificateCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : realCode (shuffleCertificateCodes D) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT ArithmeticShuffleCertificate.certificate_arith
    (fun _ => shuffleOpenCodes D) (fun _ => shuffleOpenCodes_mem M hM hT D hD)

theorem wordCode_mem_shuffleStar (D : ZFSet.{0}) (p : List Bool) :
    wordCode p ∈ shuffleStar D ↔ Certificate (shuffleOpen D) p := by
  rw [shuffleStar,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,w,hw,hc⟩
    exact wordCode_injective hw ▸ hc
  · intro hc
    exact ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,p,rfl,hc⟩

theorem shuffleStar_eq_image (D : ZFSet.{0}) :
    shuffleStar D = wordImage (shuffleCertificateCodes D) := by
  apply ZFSet.ext
  intro q
  by_cases hq : q ∈ conditions
  · obtain ⟨p,rfl⟩ := (prefix_iff_wordCode q).mp ((mem_conditions q).mp hq)
    exact (wordCode_mem_shuffleStar D p).trans
      (wordImage_spec (Certificate (shuffleOpen D)) (shuffleCertificateCodes D)
        (shuffleCertificateCodes_true D) p).symm
  · exact ⟨fun h => False.elim (hq (ZFSet.mem_sep.mp h).1),
      fun h => False.elim (hq (ZFSet.mem_sep.mp h).1)⟩

theorem shuffleStar_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : shuffleStar D ∈ M := by
  rw [shuffleStar_eq_image]
  exact wordImage_mem M hM hT _ (shuffleCertificateCodes_mem M hM hT D hD)

theorem shuffleOpen_denseOpen (D : ZFSet.{0})
    (hD : Dense {p : Condition | wordCode p.word ∈ D}) : DenseOpen (shuffleOpen D) := by
  refine ⟨?_,?_⟩
  · intro p
    obtain ⟨q,hq,hd⟩ := hD ⟨p⟩
    exact ⟨q.word,hq,q.word,hd,List.prefix_rfl⟩
  · intro p q hpq h
    obtain ⟨r,hr,hrp⟩ := h
    exact ⟨r,hr,hrp.trans hpq⟩

theorem shuffleStar_denseOpen (D : ZFSet.{0})
    (hD : Dense {p : Condition | wordCode p.word ∈ D}) :
    DenseOpen (fun p => wordCode p ∈ shuffleStar D) := by
  simpa only [wordCode_mem_shuffleStar] using
    certificate_denseOpen (shuffleOpen D) (shuffleOpen_denseOpen D hD)

theorem shuffleStar_dense (D : ZFSet.{0})
    (hD : Dense {p : Condition | wordCode p.word ∈ D}) :
    Dense {p : Condition | wordCode p.word ∈ shuffleStar D} := by
  intro p
  obtain ⟨q,hpq,hq⟩ := (shuffleStar_denseOpen D hD).1 p.word
  exact ⟨⟨q⟩,hpq,hq⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalShuffleGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
open ShuffleRequirements FiniteShuffleCertificate
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem groundGeneric_shuffle (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : Oracle) (hG : AtomicForcing.GroundGeneric M (pushFilter (realFilter G)))
    (Y : Oracle) :
    AtomicForcing.GroundGeneric M (pushFilter (realFilter (GenericCoding.code Y G))) := by
  apply (groundGeneric_iff M _).mpr
  intro D hD hd
  obtain ⟨p,hp,hstar⟩ := (groundGeneric_iff M _).mp hG (shuffleStar D)
    (shuffleStar_mem M hM hT D hD) (shuffleStar_dense D hd)
  rw [pull_push] at hp
  have hc := (wordCode_mem_shuffleStar D p.word).mp hstar
  obtain ⟨t,⟨r,hr,hrt⟩,htransfer⟩ := certificate_transfer (shuffleOpen D) p.word hc Y
  refine ⟨⟨r⟩,?_,hr⟩
  rw [pull_push]
  exact realizes_mono hrt (htransfer G hp)

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealHullColumnRealization
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCountableOrdinals
open CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem real_hull_shuffled_column_realizes_oai (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (X Y L : Oracle)
    (hXE : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hYE : realCode Y ∈ genericExtensionSet M (poset K) G.carrier)
    (hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier)
    (hL : AtomicForcing.GroundGeneric (RealGeneratedModel.hull M (realCode X))
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter L))) :
    ColumnRealizesExtension (RealGeneratedModel.hull M (realCode X)) K a
      (genericExtensionSet M (poset K) G.carrier) (GenericCoding.code Y L) := by
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  obtain ⟨hN,_,_,_⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode X) hXE (realCode_subset X)
  exact real_hull_generic_column_realizes M K a hM hT hK ha G hG X _ hXE
    (sourceT_real_lower _ hE hTE (sourceT_real_join _ hE hTE hYE hLE) (GenericCoding.code_reduces Y L))
    (InternalCohen.groundGeneric_shuffle _ hN.1 hN.2.1 L hL Y)

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes_oai := @OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes_oai
