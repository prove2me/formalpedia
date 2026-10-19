-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance_le_av
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:32:35.031795+00:00
-- url     : https://prove2.me/submissions/76d6ed74-2130-43c9-bdd7-2815b8461712

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotParameters.lean:L205-L250
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance_le_av. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_concrete_slot_variance
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

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
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

lemma shortResidues_card (q B : ℕ) : (shortResidues q B).card≤2*B+1 := by
  apply Finset.card_image_le.trans
  simp [Int.card_Icc]
  omega

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

lemma catalogSet_card (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) :
    (catalogSet d R K q).card=2*K*((R-2)*periodLength (oddLengths d)) := by
  rw [catalogSet,Finset.card_image_of_injective _ (catalogValue_injective d R K q i hq)]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- from OAI.Analysis.Littlewood.SlotParameters ----
namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

lemma chunkCount_bounds {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    B*chunkCount B q<q ∧ q≤B*(chunkCount B q+1) := by
  have hm := Nat.mod_lt (q-1) hB
  have he := Nat.mod_add_div (q-1) B
  dsimp [chunkCount]
  constructor
  · have hd := Nat.mul_div_le (q-1) B
    omega
  · nlinarith only [hm,he,show q-1+1=q by omega]

lemma chunkCount_pos {B q : ℕ} (hB : 0<B) (hq : B<q) : 0<chunkCount B q := by
  exact Nat.div_pos (by omega) hB

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

lemma concrete_slot_variance_le_av {r q : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (R : ℕ) (i₀ : Fin r) (hR : 2≤R)
    (hq' : 2*R*periodLength (oddLengths d)<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    let K := chunkCount (2*R*periodLength (oddLengths d)) q
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      packingAV r (periodLength (oddLengths d)) R q := by
  dsimp only
  let L := periodLength (oddLengths d)
  let K := chunkCount (2*R*L) q
  have hL : 0<L := periodLength_pos d i₀
  have hq0 : 0<q := (Fact.out : q.Prime).pos
  have hq : 2*(K*(R*L))<q := by
    have h := (chunkCount_bounds (show 0<2*R*L by positivity) hq0).1
    dsimp [K]
    nlinarith only [h]
  have hK : 0<K := chunkCount_pos (by positivity) hq'
  have h := concrete_slot_variance d R K i₀ hK hq g hg hpair i
  have hcat : (catalogSet d R K q).card≤q := by
    simpa only [ZMod.card] using (Finset.card_le_univ (catalogSet d R K q))
  have hc := catalogSet_card d R K q i₀ hq
  have hs : ((shortResidues q (R*L)).card : ℝ)≤2*(R : ℝ)*L+1 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_assoc] using
      (Nat.cast_le.mpr (shortResidues_card q (R*L)) : ((shortResidues q (R*L)).card : ℝ)≤((2*(R*L)+1 : ℕ) : ℝ))
  have hR2 : ((R-2 : ℕ) : ℝ)=(R : ℝ)-2 := by rw [Nat.cast_sub hR]; norm_num
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq0
  apply h.trans
  rw [Nat.cast_add,Nat.cast_sub hcat]
  simp only [hc,Nat.cast_mul,Nat.cast_ofNat,hR2]
  change 3*(2*(((r-1 : ℕ) : ℝ)*((q : ℝ)-2*(K : ℝ)*(((R : ℝ)-2)*L))/q+
      2*((r-1 : ℕ) : ℝ)^2*((shortResidues q (R*L)).card : ℝ)/q)+
      ((r-1 : ℕ) : ℝ)^2*((q : ℝ)-2*(K : ℝ)*(((R : ℝ)-2)*L)+2*(((R : ℝ)-2)*L))/q)≤_
  have hshort := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ)≤2*((r-1 : ℕ) : ℝ)^2)) hqpos.le
  dsimp [packingAV]
  change _≤3*(2*(((r-1 : ℕ) : ℝ)*(1-2*((R : ℝ)-2)*L*((K : ℝ)/q))+
      2*((r-1 : ℕ) : ℝ)^2*(2*(R : ℝ)*L+1)*(1/q))+
      ((r-1 : ℕ) : ℝ)^2*(1-2*((R : ℝ)-2)*L*((K : ℝ)/q)+2*((R : ℝ)-2)*L*(1/q)))
  have hqne := hqpos.ne'
  field_simp at hshort ⊢
  nlinarith only [hshort]

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable


theorem solution.{uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance_le_av.{uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.concrete_slot_variance_le_av.{uV}
