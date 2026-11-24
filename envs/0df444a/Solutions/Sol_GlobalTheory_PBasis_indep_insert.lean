-- Prove2me | solution 1 for GlobalTheory.PBasis.indep_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:31.377047+00:00
-- url     : https://prove2.me/submissions/ee96fd84-6917-49e3-9134-6c3928cf0cd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
import Theorems.Thm_GlobalTheory_PBasis_map_graphRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]
namespace GlobalTheory.PBasis
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) {B : Set k} (hB : Indep p B) {a : k}
    (ha : a ∉ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)) : Indep p (insert a B) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g hg z hz h1
  have hga : g a ^ p = f a := hg a (Set.mem_insert _ _)
  have hI := hB Q f g (fun b hb => hg b (Set.mem_insert_of_mem _ hb))
  set S := graphRing p f g B with hS
  let K := powField hp.ne_zero B
  have hK : ∀ s : S, (s : k × Q).1 ∈ K := by
    intro s
    change _ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rw [← map_graphRing p f g B]
    exact ⟨s, s.2, rfl⟩
  let ψ : S →+* K := ((RingHom.fst k Q).comp S.subtype).codRestrict K hK
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have h1 : (s : k × Q).1 = 0 := congrArg Subtype.val hs
    exact Subtype.ext (Prod.ext h1 (hI s s.2 h1))
  let ev : S[X] →+* k × Q := eval₂RingHom S.subtype (a, g a)
  have hle : graphRing p f g (insert a B) ≤ ev.range := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl | hx, rfl⟩)
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩, by simp [ev]⟩
    · exact ⟨X, by simp [ev]⟩
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)⟩, by simp [ev]⟩
  obtain ⟨P, rfl⟩ := hle hz
  let c : S := ⟨(a ^ p, f a), Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩
  have hq : (X ^ p - C c : S[X]).Monic := monic_X_pow_sub_C c hp.ne_zero
  have hevq : ev (X ^ p - C c) = 0 := by
    simp [ev, c, hga]
  have hR : ev (P %ₘ (X ^ p - C c)) = ev P := by
    conv_rhs => rw [← modByMonic_add_div P (X ^ p - C c)]
    rw [map_add, map_mul, hevq, zero_mul, add_zero]
  have hirr : Irreducible (X ^ p - C (ψ c) : K[X]) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    have h2 : (b : k) ^ p = a ^ p := congrArg Subtype.val hb
    have h3 : (b : k) = a := frobenius_inj k p h2
    exact ha (h3 ▸ b.2)
  have haev : ∀ T : S[X], aeval a (T.map ψ) = (ev T).1 := by
    intro T
    rw [aeval_def, eval₂_map]
    change _ = RingHom.fst k Q (eval₂ S.subtype (a, g a) T)
    rw [hom_eval₂]
    rfl
  have hmapq : (X ^ p - C c : S[X]).map ψ = X ^ p - C (ψ c) := by simp
  have hmin : X ^ p - C (ψ c) = minpoly K a :=
    minpoly.eq_of_irreducible_of_monic hirr (by rw [← hmapq, haev, hevq]; rfl)
      (monic_X_pow_sub_C _ hp.ne_zero)
  have hdvd : (X ^ p - C c : S[X]).map ψ ∣ (P %ₘ (X ^ p - C c)).map ψ := by
    rw [hmapq, hmin]
    exact minpoly.dvd K a (by rw [haev, hR, h1])
  haveI : Nontrivial S := ψ.domain_nontrivial
  have hz0 : (P %ₘ (X ^ p - C c)).map ψ = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hdvd
    rw [degree_map_eq_of_injective hψ, degree_map_eq_of_injective hψ]
    exact degree_modByMonic_lt P hq
  rw [Polynomial.map_eq_zero_iff hψ] at hz0
  rw [← hR, hz0, map_zero]
  rfl
end GlobalTheory.PBasis
