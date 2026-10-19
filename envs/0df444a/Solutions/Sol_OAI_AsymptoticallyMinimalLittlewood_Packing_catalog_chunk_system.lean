-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.catalog_chunk_system
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:15:12.594983+00:00
-- url     : https://prove2.me/submissions/42cb3167-e547-4c08-a435-eda40a2e964f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean:L375-L432
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.catalog_chunk_system. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_interior_center_exists
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signedSite_injective
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_siteCenter_chunk

-- ---- from OAI.Analysis.Littlewood.Chunks ----
namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

variable {r : ℕ}
lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma slotLeft_bounds (L : Fin r → ℕ) (R : ℕ) {shift chunk period : ℕ}
    (hs : shift<periodLength L) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength L) ≤ slotLeft L R shift chunk period i ∧
    slotLeft L R shift chunk period i+L i < (chunk+1)*(R*periodLength L) := by
  have hi := prefix_add_length_le L i
  have hp' : (period+2)*periodLength L ≤ R*periodLength L :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [slotLeft]
  constructor
  · omega
  · simp only [Nat.add_mul] at hp' ⊢
    omega

lemma siteCenter_bounds (d : Fin r → ℕ) {R shift chunk period : ℕ}
    (hs : shift<periodLength (oddLengths d)) (hp : period+1<R) (i : Fin r) :
    chunk*(R*periodLength (oddLengths d)) < siteCenter d R shift chunk period i ∧
    siteCenter d R shift chunk period i < (chunk+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨hlo,hhi⟩ := slotLeft_bounds (oddLengths d) R (chunk := chunk) hs hp i
  dsimp [siteCenter,oddLengths] at *
  omega

lemma interiorSite_bounds (d : Fin r → ℕ) {R k t : ℕ} (i : Fin r)
    (ht : t<(R-2)*periodLength (oddLengths d)) :
    k*(R*periodLength (oddLengths d)) < interiorSite d R k t ∧
    interiorSite d R k t < (k+1)*(R*periodLength (oddLengths d)) := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d ht i
  have he' : interiorSite d R k t=siteCenter d R s k p i := by
    dsimp [interiorSite,siteCenter,slotLeft]
    omega
  rw [he']
  exact siteCenter_bounds d hs hp i

lemma interiorSite_chunk (d : Fin r → ℕ) {R k t : ℕ} (i : Fin r)
    (ht : t<(R-2)*periodLength (oddLengths d)) :
    interiorSite d R k t/(R*periodLength (oddLengths d))=k := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d ht i
  have he' : interiorSite d R k t=siteCenter d R s k p i := by
    dsimp [interiorSite,siteCenter,slotLeft]
    omega
  rw [he']
  exact siteCenter_chunk d hs hp i

lemma interior_signed_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    Function.Injective (fun x : (Fin K × Fin ((R-2)*periodLength (oddLengths d))) × Bool ↦
      signedSite q x.2 (interiorSite d R x.1.1 x.1.2)) := by
  rintro ⟨⟨k,t⟩,e⟩ ⟨⟨l,u⟩,f⟩ he
  have hk := interiorSite_bounds d (k := (k : ℕ)) i t.isLt
  have hl := interiorSite_bounds d (k := (l : ℕ)) i u.isLt
  have hk' : interiorSite d R k t ≤ K*(R*periodLength (oddLengths d)) :=
    hk.2.le.trans (Nat.mul_le_mul_right _ (by omega))
  have hl' : interiorSite d R l u ≤ K*(R*periodLength (oddLengths d)) :=
    hl.2.le.trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨hef,he'⟩ := (signedSite_injective hq (by omega) hk' (by omega) hl' e f).mp he
  have hkl : (k : ℕ)=(l : ℕ) := by
    have hc := congrArg (fun c ↦ c/(R*periodLength (oddLengths d))) he'
    simpa only [interiorSite_chunk d i t.isLt,interiorSite_chunk d i u.isLt] using hc
  have htu : (t : ℕ)=(u : ℕ) := by
    dsimp [interiorSite] at he'
    rw [hkl] at he'
    omega
  cases Fin.ext hkl
  cases Fin.ext htu
  cases hef
  rfl

lemma interior_hit_coordinate (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    (k : Fin K) (t : Fin ((R-2)*periodLength (oddLengths d))) (e : Bool) :
    ∃ s : Fin (periodLength (oddLengths d)), ∀ ω : SlotChoices d K,
      slotHit d R K q i ω (signedSite q e (interiorSite d R k t)) ↔ ω k=(s,e) := by
  obtain ⟨p,s,hp,hs,he⟩ := interior_center_exists d t.isLt i
  let p₀ : Fin (R-1) := ⟨p,by omega⟩
  let s₀ : Fin (periodLength (oddLengths d)) := ⟨s,hs⟩
  have he' : interiorSite d R k t=siteCenter d R s₀ k p₀ i := by
    dsimp [interiorSite,siteCenter,slotLeft,s₀,p₀]
    omega
  refine ⟨s₀,?_⟩
  intro ω
  constructor
  · rintro ⟨l,u,hu⟩
    have hk := interiorSite_bounds d (k := (k : ℕ)) i t.isLt
    have hl := siteCenter_bounds d (R := R) (chunk := (l : ℕ)) (period := (u : ℕ)) (ω l).1.isLt (by have := u.isLt; omega) i
    have hk' : interiorSite d R k t≤K*(R*periodLength (oddLengths d)) :=
      hk.2.le.trans (Nat.mul_le_mul_right _ (by omega))
    have hl' : siteCenter d R (ω l).1 l u i≤K*(R*periodLength (oddLengths d)) :=
      hl.2.le.trans (Nat.mul_le_mul_right _ (by omega))
    obtain ⟨hes,hc⟩ := (signedSite_injective hq (by omega) hk' (by omega) hl' e (ω l).2).mp hu
    have hkl : (k : ℕ)=(l : ℕ) := by
      have hc' := congrArg (fun n ↦ n/(R*periodLength (oddLengths d))) hc
      simpa only [interiorSite_chunk d i t.isLt,
        siteCenter_chunk d (R := R) (period := (u : ℕ)) (ω l).1.isLt (by have := u.isLt; omega) i] using hc'
    have hkl' : k=l := Fin.ext hkl
    subst l
    have hp' : p*periodLength (oddLengths d)+s=
        (u : ℕ)*periodLength (oddLengths d)+(ω k).1 := by
      rw [he'] at hc
      dsimp [siteCenter,slotLeft,p₀,s₀] at hc
      omega
    have hmod := congrArg (fun n ↦ n%periodLength (oddLengths d)) hp'
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hs, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt (ω k).1.isLt] at hmod
    apply Prod.ext
    · exact Fin.ext hmod.symm
    · exact hes.symm
  · intro hω
    refine ⟨k,p₀,?_⟩
    rw [hω]
    exact congrArg (signedSite q e) he'

lemma same_chunk_collision (d : Fin r → ℕ) (R q : ℕ) (i : Fin r)
    {k t u : ℕ} (ht : t<(R-2)*periodLength (oddLengths d))
    (hu : u<(R-2)*periodLength (oddLengths d)) (e f : Bool) :
    signedSite q e (interiorSite d R k t)+signedSite q f (interiorSite d R k u)
      ∈shortResidues q (R*periodLength (oddLengths d)) ∨
    signedSite q e (interiorSite d R k t)-signedSite q f (interiorSite d R k u)
      ∈shortResidues q (R*periodLength (oddLengths d)) := by
  have ht' := interiorSite_bounds d (k := k) i ht
  have hu' := interiorSite_bounds d (k := k) i hu
  simp only [Nat.add_mul, Nat.one_mul] at ht' hu'
  let a : ℤ := interiorSite d R k t
  let b : ℤ := interiorSite d R k u
  have hdiff : a-b∈Finset.Icc (-(R*periodLength (oddLengths d) : ℕ) : ℤ)
      (R*periodLength (oddLengths d)) := by
    simp only [Finset.mem_Icc]
    dsimp [a,b]

    constructor <;> omega
  have hdiff' : b-a∈Finset.Icc (-(R*periodLength (oddLengths d) : ℕ) : ℤ)
      (R*periodLength (oddLengths d)) := by
    simp only [Finset.mem_Icc] at hdiff ⊢
    constructor <;> omega
  have hd : ((a-b : ℤ) : ZMod q)∈shortResidues q (R*periodLength (oddLengths d)) :=
    Finset.mem_image.mpr ⟨a-b,hdiff,rfl⟩
  have hd' : ((b-a : ℤ) : ZMod q)∈shortResidues q (R*periodLength (oddLengths d)) :=
    Finset.mem_image.mpr ⟨b-a,hdiff',rfl⟩
  dsimp [a,b] at hd hd'
  push_cast at hd hd'
  cases e <;> cases f <;> simp only [signedSite,Bool.false_eq_true,↓reduceIte]
  · exact Or.inr (by simpa only [sub_eq_add_neg,neg_neg,add_comm] using hd')
  · exact Or.inl (by simpa only [sub_eq_add_neg,add_comm] using hd')
  · exact Or.inl (by simpa only [sub_eq_add_neg] using hd)
  · exact Or.inr hd

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

lemma catalogValue_injective (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    Function.Injective (catalogValue d R K q) := by
  rintro ⟨k,t,b⟩ ⟨l,u,e⟩ h
  have hh : ((k,t),b)=((l,u),e) := interior_signed_injective d R K q i hq h
  obtain ⟨hkt,hbe⟩ := Prod.mk.inj hh
  cases hkt
  cases hbe
  rfl

lemma catalog_chunk_system (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i₀ : Fin r)
    (hK : 0<K) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    ∃ chunk : ZMod q → Fin K,
      (∀ c : InteriorCatalog d R K, chunk (catalogValue d R K q c)=c.1) ∧
      (∀ i t, t∈catalogSet d R K q →
        ∃ a : Fin (periodLength (oddLengths d)) × Bool,
          ∀ ω : SlotChoices d K, slotHit d R K q i ω t ↔ ω (chunk t)=a) ∧
      (∀ k, (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)).card≤
        q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) ∧
      (∀ t∈catalogSet d R K q, ∀ u∈catalogSet d R K q, chunk t=chunk u →
        t+u∈shortResidues q (R*periodLength (oddLengths d)) ∨
        t-u∈shortResidues q (R*periodLength (oddLengths d))) := by
  classical
  let chunk : ZMod q → Fin K := fun t ↦
    if h : ∃ c : InteriorCatalog d R K, catalogValue d R K q c=t then h.choose.1
    else ⟨0,hK⟩
  have hinj := catalogValue_injective d R K q i₀ hq
  have hchunk (c : InteriorCatalog d R K) : chunk (catalogValue d R K q c)=c.1 := by
    dsimp [chunk]
    split_ifs with h
    · exact congrArg Prod.fst (hinj h.choose_spec)
    · exact (h ⟨c,rfl⟩).elim
  refine ⟨chunk,hchunk,?_,?_,?_⟩
  · intro i t ht
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s,hs⟩ := interior_hit_coordinate d R K q i hq c.1 c.2.1 c.2.2
    refine ⟨(s,c.2.2),?_⟩
    rw [hchunk]
    exact hs
  · intro k
    let T : Finset (ZMod q) := Finset.univ.image (fun c :
      Fin ((R-2)*periodLength (oddLengths d)) × Bool ↦ catalogValue d R K q (k,c))
    have hsub : (Finset.univ.filter (fun t : ZMod q ↦ chunk t=k)) ⊆
        ((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q) ∪ T := by
      intro t ht
      by_cases hg : t∈catalogSet d R K q
      · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hg
        have hk : c.1=k := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,hchunk] using ht
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨c.2,Finset.mem_univ _,by cases hk; rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hg⟩)
    have hT : T.card≤2*((R-2)*periodLength (oddLengths d)) := by
      apply Finset.card_image_le.trans_eq
      simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
      ring
    calc
      _ ≤ (((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q) ∪ T).card := Finset.card_le_card hsub
      _ ≤ ((Finset.univ : Finset (ZMod q)) \ catalogSet d R K q).card+T.card := Finset.card_union_le _ _
      _ ≤ _ := by
        rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,ZMod.card]
        omega
  · intro t ht u hu htu
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    have hce : c.1=e.1 := by simpa only [hchunk] using htu
    dsimp [catalogValue]
    rw [hce]
    exact same_chunk_collision d R q i₀ c.2.1.isLt e.2.1.isLt c.2.2 e.2.2

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.catalog_chunk_system := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.catalog_chunk_system
