-- Prove2me | solution 1 for GlobalTheory.CuspGL.rootSum_charpoly_mem_virt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:09.935454+00:00
-- url     : https://prove2.me/submissions/adfae8ea-4bff-4e92-b385-549187da6b6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterBrauerLiftAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGL
import Theorems.Thm_GlobalTheory_BI_AbByP_subgroup
import Theorems.Thm_GlobalTheory_BI_ind_mul_classFun_eq_ind_mul_restrict
import Theorems.Thm_GlobalTheory_BI_isChar_esymm_roots_charpoly
import Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
import Theorems.Thm_GlobalTheory_BI_isChar_one
import Theorems.Thm_GlobalTheory_BI_matrixChar_iff_isChar
import Theorems.Thm_GlobalTheory_BI_one_mem_closure_ind_centralByPrime
import Theorems.Thm_GlobalTheory_BI_virt_mul_comap_conj_ind_linear
import Theorems.Thm_GlobalTheory_CharpolyPow_card_roots_charpoly
import Theorems.Thm_GlobalTheory_CharpolyPow_roots_charpoly_pow
import Theorems.Thm_GlobalTheory_CuspGL_isChar_brauerLift
import Theorems.Thm_GlobalTheory_HasLogGrowth_comp
import Theorems.Thm_GlobalTheory_IsLogBoundedScalar_comp
import Theorems.Thm_GlobalTheory_IsLogBounded_comp
import Theorems.Thm_GlobalTheory_multiset_newton_psum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL
open Polynomial in
private theorem sylow_normal_of_prime_pow_mem_center (E : Type) [Group E] [Finite E] (p : ℕ) [hp : Fact p.Prime] (P : Sylow p E)
    (hE : ∀ (y : E), ∃ j, y ^ p ^ j ∈ Subgroup.center E) : (P : Subgroup E).Normal := by
  have hpq : IsPGroup p (E ⧸ Subgroup.center E) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨j, hj⟩ := hE y
      exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  obtain ⟨c, hc⟩ := hpq.exists_card_eq
  have hS : Subgroup.center E ⊔ (P : Subgroup E) = ⊤ := by
    apply Subgroup.index_eq_one.1
    have h1 : (Subgroup.center E ⊔ (P : Subgroup E)).index ∣ p ^ c := by
      rw [← hc]
      exact Subgroup.index_dvd_of_le le_sup_left
    have h2 : (Subgroup.center E ⊔ (P : Subgroup E)).index ∣ (P : Subgroup E).index :=
      Subgroup.index_dvd_of_le le_sup_right
    have hcop : Nat.Coprime (p ^ c) (P : Subgroup E).index :=
      Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp.out).2 P.not_dvd_index)
    exact Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h1 h2)
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hS]
  exact sup_le (Subgroup.center_le_normalizer _) Subgroup.le_normalizer
open Polynomial in
private theorem exists_p_regular_split_of_normal_sylow_commute (E : Type) [Group E] [Finite E] (p : ℕ) [Fact p.Prime] (P : Sylow p E) [(P : Subgroup E).Normal]
    (hcomm : ∀ x y : E, x ∈ (P : Subgroup E) → ¬ p ∣ orderOf y → Commute y x) :
    ∃ H : Subgroup E, ∃ π : E →* H, ¬ p ∣ Nat.card H ∧
      ∀ g, ∃ s, ∃ m : ℕ, g = (π g : E) * s ∧ Commute (π g : E) s ∧ s ^ p ^ m = 1 := by
  obtain ⟨H, hPH⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  have hHP := hPH.symm
  refine ⟨H, hHP.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' (P : Subgroup E)), ?_, ?_⟩
  · have h1 := hPH.card_mul
    have h2 := (P : Subgroup E).card_mul_index
    have h3 : Nat.card H = (P : Subgroup E).index := by
      have hpos : 0 < Nat.card (P : Subgroup E) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact P.not_dvd_index
  · intro g
    set h : H := hHP.QuotientMulEquiv (g : E ⧸ (P : Subgroup E)) with hh
    have hq : (g : E ⧸ (P : Subgroup E)) = QuotientGroup.mk ((h : H) : E) := by
      conv_lhs => rw [← hHP.QuotientMulEquiv.symm_apply_apply (g : E ⧸ (P : Subgroup E))]
      rfl
    have hs : ((h : E))⁻¹ * g ∈ (P : Subgroup E) := by
      have := QuotientGroup.eq.1 hq.symm
      exact this
    obtain ⟨m, hm⟩ := P.2 ⟨_, hs⟩
    refine ⟨((h : E))⁻¹ * g, m, ?_, ?_, ?_⟩
    · simp [h]
    · apply hcomm _ _ hs
      intro hp
      have hd : orderOf (h : E) ∣ Nat.card H := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard h
      have h1 := hPH.card_mul
      have h2 := (P : Subgroup E).card_mul_index
      have h3 : Nat.card H = (P : Subgroup E).index :=
        Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
      exact P.not_dvd_index (h3 ▸ hp.trans hd)
    · have := congrArg Subtype.val hm
      simpa using this
open Polynomial in
private theorem exists_p_regular_split_of_pow_mem_center (E : Type) [Group E] [Finite E] (p : ℕ) [hp : Fact p.Prime]
    (hE : ∃ l, Nat.Prime l ∧ ∀ (y : E), ∃ j, y ^ l ^ j ∈ Subgroup.center E) :
    ∃ H : Subgroup E, ∃ π : E →* H, ¬ p ∣ Nat.card H ∧
      ∀ g, ∃ s, ∃ m : ℕ, g = (π g : E) * s ∧ Commute (π g : E) s ∧ s ^ p ^ m = 1 := by
  obtain ⟨l, hl, hy⟩ := hE
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p E))
  have hcen : ∀ y : E, Nat.Coprime l (orderOf y) → y ∈ Subgroup.center E := by
    intro y hco
    obtain ⟨j, hj⟩ := hy y
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.Coprime.pow_left j hco)
    rw [← hm]
    exact Subgroup.pow_mem _ hj m
  by_cases hlp : l = p
  · subst hlp
    haveI := sylow_normal_of_prime_pow_mem_center E l P hy
    apply exists_p_regular_split_of_normal_sylow_commute E l P
    intro x y _ hyo
    have := hcen y ((Nat.Prime.coprime_iff_not_dvd hl).2 hyo)
    exact (Subgroup.mem_center_iff.1 this x).symm
  · have hPc : ∀ x ∈ (P : Subgroup E), x ∈ Subgroup.center E := by
      intro x hx
      obtain ⟨a, ha⟩ := P.2 ⟨x, hx⟩
      have ha' : x ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
      apply hcen
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ha')
        (Nat.Coprime.pow_right a ((Nat.coprime_primes hl hp.out).2 hlp))
    haveI : (P : Subgroup E).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_center_iff.1 (hPc n hn) g, mul_inv_cancel_right]; exact hn⟩
    apply exists_p_regular_split_of_normal_sylow_commute E p P
    intro x y hx _
    exact Subgroup.mem_center_iff.1 (hPc x hx) y
open Polynomial in
private theorem powerSum_roots_charpoly_complex_mem_virt (G : Type) [Group G] [Finite G] (n : ℕ) (ρ : G →* GL (Fin n) ℂ) (r : ℕ) :
    (fun g => (Multiset.map (fun x => x ^ r) ((ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots)).sum)
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
  have hmul := (_root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear G).1
  have he : ∀ j, (fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots.esymm j)
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := fun j =>
    _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_esymm_roots_charpoly G n j ρ)
  have hconst : ∀ c : ℤ, (fun _ : G => (c : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
    intro c
    have h1 : (fun _ : G => (1 : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G :=
      _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_one ℂ ℂ G)
    have := zsmul_mem h1 c
    convert this using 1
    funext g
    simp
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · convert hconst n using 1
      funext g
      simp [_root_.GlobalTheory.CharpolyPow.card_roots_charpoly]
    · have rootSum_charpoly_mem_virt_of_pow_mem_center : (fun g => (Multiset.map (fun x => x ^ r) ((ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots)).sum)
          = (fun _ => (((-1) ^ (r + 1) * r : ℤ) : ℂ)) * (fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots.esymm r)
            - ∑ i ∈ Finset.Ioo 0 r, ((fun _ => (((-1) ^ i : ℤ) : ℂ)) * (fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots.esymm i)
              * (fun g => (Multiset.map (fun x => x ^ (r - i)) ((ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots)).sum)) := by
        funext g
        rw [_root_.GlobalTheory.multiset_newton_psum _ r hr]
        simp [Finset.sum_apply]
      rw [rootSum_charpoly_mem_virt_of_pow_mem_center]
      refine sub_mem (hmul _ (hconst _) _ (he r)) (sum_mem fun i hi => ?_)
      have hi' := Finset.mem_Ioo.1 hi
      exact hmul _ (hmul _ (hconst _) _ (he i)) _ (ih (r - i) (by omega))
open Polynomial in
private theorem powerSum_roots_charpoly_mem_virt_of_abByP (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (H : Type) [Group H] [Finite H]
    (hab : _root_.GlobalTheory.BI.AbByP H) (hc : (Nat.card H : k) ≠ 0) (n : ℕ) (ρ : H →* GL (Fin n) k) (r : ℕ) :
    (fun g => (Multiset.map (fun α => θ α ^ r) ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots)).sum)
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H := by
  obtain ⟨m, ρC, hC⟩ := (_root_.GlobalTheory.BI.matrixChar_iff_isChar H _).2
    (_root_.GlobalTheory.CuspGL.isChar_brauerLift k θ hθ H hab hc n ρ)
  convert powerSum_roots_charpoly_complex_mem_virt H m ρC r using 1
  funext g
  have h1 : Multiset.map (fun α => θ α ^ r) ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots)
      = Multiset.map θ ((ρ (g ^ r) : Matrix (Fin n) (Fin n) k).charpoly.roots) := by
    rw [map_pow, Units.val_pow_eq_pow_val, _root_.GlobalTheory.CharpolyPow.roots_charpoly_pow, Multiset.map_map]
    simp [Function.comp_def, map_pow]
  have h2 := hC (g ^ r)
  rw [h1, h2, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
    _root_.GlobalTheory.CharpolyPow.roots_charpoly_pow]
open Polynomial in
private theorem powerSum_roots_charpoly_mem_virt_of_split (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (E : Type) [Group E] [Finite E]
    (hab : _root_.GlobalTheory.BI.AbByP E) (H : Subgroup E) (π : E →* H) (hc : (Nat.card H : k) ≠ 0)
    (hdec : ∀ g, ∃ s, ∃ m : ℕ, g = (π g : E) * s ∧ Commute (π g : E) s ∧ s ^ p ^ m = 1)
    (n : ℕ) (ρ : E →* GL (Fin n) k) (r : ℕ) :
    (fun g => (Multiset.map (fun α => θ α ^ r) ((ρ g : Matrix (Fin n) (Fin n) k).charpoly.roots)).sum)
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ E := by
  have hH := powerSum_roots_charpoly_mem_virt_of_abByP k θ hθ H (_root_.GlobalTheory.BI.AbByP.subgroup E H hab) hc n
    (ρ.comp H.subtype) r
  have := (_root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear H).2.1 _ hH E π
  convert this using 1
  funext g
  obtain ⟨s, m, hg, hcs, hs⟩ := hdec g
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  congr 2
  conv_lhs => rw [hg]
  rw [map_mul, Units.val_mul]
  have hinj : Function.Injective (fun x : k => x ^ p ^ m) := iterateFrobenius_inj k p m
  apply Multiset.map_injective hinj
  rw [← _root_.GlobalTheory.CharpolyPow.roots_charpoly_pow, ← _root_.GlobalTheory.CharpolyPow.roots_charpoly_pow]
  have hc' : Commute (ρ (π g : E) : Matrix (Fin n) (Fin n) k) (ρ s : Matrix (Fin n) (Fin n) k) := by
    have := (hcs.map ρ).units_val
    exact this
  rw [hc'.mul_pow, ← Units.val_pow_eq_pow_val (ρ s), ← map_pow, hs, map_one, Units.val_one, mul_one]
open Polynomial in
private theorem rootSum_charpoly_mem_virt_of_pow_mem_center (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ)
    (E : Subgroup (GL (Fin n) F)) (hE : ∃ l, Nat.Prime l ∧ ∀ (y : E), ∃ j, y ^ l ^ j ∈ Subgroup.center E) :
    (fun x : E => _root_.GlobalTheory.CuspGL.rootSum θ k (Matrix.charpoly ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ E := by
  obtain ⟨p, hchar⟩ := CharP.exists F
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  haveI : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hab : _root_.GlobalTheory.BI.AbByP E := by
    obtain ⟨l, hl, hy⟩ := hE
    exact ⟨l, hl, Subgroup.center E, inferInstance,
      fun a ha b _ => (Subgroup.mem_center_iff.1 ha b).symm, hy⟩
  obtain ⟨H, π, hnd, hdec⟩ := exists_p_regular_split_of_pow_mem_center E p hE
  let ρ : E →* GL (Fin n) (AlgebraicClosure F) :=
    (Units.map (algebraMap F (AlgebraicClosure F)).mapMatrix.toMonoidHom).comp E.subtype
  have hc : (Nat.card H : AlgebraicClosure F) ≠ 0 := (CharP.cast_eq_zero_iff _ p _).not.2 hnd
  convert powerSum_roots_charpoly_mem_virt_of_split (AlgebraicClosure F) p θ hθ E hab H π hc hdec n ρ k using 1
  funext x
  unfold _root_.GlobalTheory.CuspGL.rootSum
  congr 3
  simp [ρ, Matrix.charpoly_map]
end GlobalTheory.CuspGL
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
open Polynomial
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ) :
    (fun x : GL (Fin n) F => _root_.GlobalTheory.CuspGL.rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)))
      ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F) := by
  set χ : GL (Fin n) F → ℂ := fun x => _root_.GlobalTheory.CuspGL.rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)) with hχ
  obtain ⟨hmul, -, -, hind, -⟩ := _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear (GL (Fin n) F)
  have hcl : ∀ (g x : GL (Fin n) F), χ (x⁻¹ * g * x) = χ g := by
    intro g x
    show _root_.GlobalTheory.CuspGL.rootSum θ k _ = _root_.GlobalTheory.CuspGL.rootSum θ k _
    congr 1
    simpa [Units.val_mul] using Matrix.charpoly_units_conj' x (g : Matrix (Fin n) (Fin n) F)
  have h1 := _root_.GlobalTheory.BI.one_mem_closure_ind_centralByPrime (GL (Fin n) F)
  have H := AddSubgroup.closure_induction (p := fun φ _ => φ * χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F))
    (fun φ hφ => by
      obtain ⟨E, ψ, hE, hψ, rfl⟩ := hφ
      rw [_root_.GlobalTheory.BI.ind_mul_classFun_eq_ind_mul_restrict _ E ψ χ hcl]
      exact hind E _ ((_root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear E).1 _ hψ _ (rootSum_charpoly_mem_virt_of_pow_mem_center F θ hθ n k E hE)))
    (by simpa using (_root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F)).zero_mem)
    (fun a b _ _ ha hb => by rw [add_mul]; exact add_mem ha hb)
    (fun a _ ha => by rw [neg_mul]; exact neg_mem ha) h1
  simpa using H
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
