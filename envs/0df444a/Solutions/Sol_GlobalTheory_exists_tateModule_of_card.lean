-- Prove2me | solution 1 for GlobalTheory.exists_tateModule_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:57.926083+00:00
-- url     : https://prove2.me/submissions/e5de6406-75f8-45ec-8cba-6b7cbb48a921

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Theorems.Thm_GlobalTheory_TateSeq_zsmul_congr
import Theorems.Thm_GlobalTheory_TateSeq_exists_div
import Theorems.Thm_GlobalTheory_TateSeq_exists_basis
import Theorems.Thm_GlobalTheory_TateSeq_exists_tower
import Theorems.Thm_GlobalTheory_TateSeq_tower_pow
import Theorems.Thm_GlobalTheory_TateSeq_tower_indep
import Theorems.Thm_GlobalTheory_TateSeq_tower_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TateSeq
namespace GlobalTheory
theorem _root_.solution :
    ∀ (M : Type) [AddCommGroup M] (l r : ℕ) [Fact l.Prime], (∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (r * n)) → ∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℤ_[l] T) (π : ℕ → T →+ M), Module.Free ℤ_[l] T ∧ Module.Finite ℤ_[l] T ∧ Module.finrank ℤ_[l] T = r ∧ (∀ n x, l • π (n + 1) x = π n x) ∧ (∀ x, π 0 x = 0) ∧ (∀ n (a : ℤ_[l]) x, π n (a • x) = (PadicInt.toZModPow n a).val • π n x) ∧ (∀ n y, l ^ n • y = 0 → ∃ x, π n x = y) ∧ (∀ n x, π n x = 0 ↔ ∃ y, x = l ^ n • y) ∧ ∀ s : ℕ → M, s 0 = 0 → (∀ n, l • s (n + 1) = s n) → ∃! x, ∀ n, π n x = s n := by
  intro M _ l r _ h
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_basis (M := M) l r (by simpa using h 1)
  choose e' he0 he1 he using fun i => exists_tower l (exists_div l r h) (b i) (hb0 i)
  let e : ℕ → Fin r → M := fun n i => e' i n
  have he' : ∀ n i, l • e (n + 1) i = e n i := fun n i => he i n
  have hind := tower_indep he' (by simpa [e, he1] using hb1)
  have hspan := tower_span he' (by simpa [e, he1] using hb2)
  have hkill : ∀ n i, l ^ n • e n i = 0 := fun n i => by
    have := tower_pow (he i) n 0
    rwa [zero_add, he0] at this
  let c : ℕ → ℤ_[l] → ℤ := fun n a => ((PadicInt.toZModPow n a).val : ℤ)
  have hc : ∀ n a, ((c n a : ℤ) : ZMod (l ^ n)) = PadicInt.toZModPow n a := fun n a => by
    simp [c]
  let π : ℕ → (Fin r → ℤ_[l]) →+ M := fun n =>
    { toFun := fun x => ∑ i, c n (x i) • e n i
      map_zero' := by simp [c]
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul]
        apply zsmul_congr (hkill n i)
        push_cast
        simp only [hc, Pi.add_apply, map_add] }
  have hπ : ∀ n (x : Fin r → ℤ_[l]) (a : Fin r → ℤ),
      (∀ i, PadicInt.toZModPow n (x i) = (a i : ZMod (l ^ n))) → π n x = ∑ i, a i • e n i := by
    intro n x a ha
    show ∑ i, c n (x i) • e n i = _
    refine Finset.sum_congr rfl fun i _ => zsmul_congr (hkill n i) ?_
    rw [hc, ha]
  have hker : ∀ n x, π n x = 0 → ∀ i, PadicInt.toZModPow n (x i) = 0 := by
    intro n x hx i
    rw [← hc, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hind n _ hx i
  refine ⟨Fin r → ℤ_[l], inferInstance, inferInstance, π, inferInstance, inferInstance,
    by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    rw [hπ n x (fun i => c (n + 1) (x i))]
    · show l • ∑ i, c (n + 1) (x i) • e (n + 1) i = _
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, he']
    · intro i
      rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n)]
      simp [c]
  · intro x
    show ∑ i, c 0 (x i) • e 0 i = 0
    simp [e, he0]
  · intro n a x
    rw [hπ n (a • x) (fun i => c n a * c n (x i))]
    · show _ = _ • ∑ i, c n (x i) • e n i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
      simp only [c, natCast_zsmul]
    · intro i
      push_cast
      simp [hc]
  · intro n y hy
    obtain ⟨a, ha⟩ := hspan n y hy
    exact ⟨fun i => (a i : ℤ_[l]), by rw [hπ n _ a (fun i => by simp), ha]⟩
  · intro n x
    constructor
    · intro hx
      have : ∀ i, ∃ y : ℤ_[l], y * (l : ℤ_[l]) ^ n = x i := fun i => by
        have h1 : x i ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hker n x hx i
        rwa [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h1
      choose y hy using this
      refine ⟨y, funext fun i => ?_⟩
      simp [← hy, mul_comm]
    · rintro ⟨y, rfl⟩
      rw [map_nsmul]
      show l ^ n • ∑ i, c n (y i) • e n i = 0
      rw [Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_comm, hkill, smul_zero]
  · intro s hs0 hs
    have hsk : ∀ n, l ^ n • s n = 0 := fun n => by
      have := tower_pow hs n 0
      rwa [zero_add, hs0] at this
    choose a ha using fun n => hspan n (s n) (hsk n)
    have hdv : ∀ i n, (l : ℤ) ^ n ∣ a (n + 1) i - a n i := by
      intro i n
      refine hind n (fun i => a (n + 1) i - a n i) ?_ i
      simp only [sub_smul, Finset.sum_sub_distrib, ha]
      rw [sub_eq_zero, ← hs n, ← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, he']
    refine ⟨fun i => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => a n i) l (hdv i)), ?_, ?_⟩
    · intro n
      rw [hπ n _ (a n) (fun i =>
        PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => a n i) l (hdv i) n), ha]
    · intro y hy
      funext i
      rw [← PadicInt.ext_of_toZModPow]
      intro n
      rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => a n i) l (hdv i) n,
        ← hc, ZMod.intCast_eq_intCast_iff_dvd_sub]
      push_cast
      refine hind n (fun i => a n i - c n (y i)) ?_ i
      simp only [sub_smul, Finset.sum_sub_distrib, ha]
      rw [sub_eq_zero, ← hy n]
      rfl
end GlobalTheory
