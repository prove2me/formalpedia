-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:25.613908+00:00
-- url     : https://prove2.me/submissions/4ab0510d-0814-4e4f-bf6c-b0debf9156a5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLattice
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetMod_sum_out
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.CosetMod
private theorem addChar_sum_eq_one_of_forall {R ι : Type} [CommRing R] (ψ : AddChar R ℂ) (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, ψ (f i) = 1) : ψ (∑ i ∈ s, f i) = 1 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, h a (Finset.mem_insert_self a s),
    ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), one_mul]
end GlobalTheory.CompanionTheory.CosetMod
end

set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetMod
namespace GlobalTheory.CompanionTheory.CosetMod
theorem _root_.solution : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  intro R _ _ _ _ _ _ ψ O u κ _ v hG hv
  classical
  let L : AddSubgroup (κ → R) := AddSubgroup.pi Set.univ (fun _ => O.toAddSubgroup)
  have memL : ∀ y : κ → R, y ∈ L ↔ ∀ i, y i ∈ O := by
    intro y; simp [L, AddSubgroup.mem_pi]
  let Gs : AddSubgroup (κ → R) :=
    L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ * v : Rˣ)) : R))
  let Hs : AddSubgroup (κ → R) :=
    L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ : Rˣ)) : R))
  have memG : ∀ y : κ → R, y ∈ Gs ↔ ∀ i, (((u⁻¹ * v : Rˣ)) : R) * y i ∈ O := by
    intro y; simp only [Gs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL,
      Pi.smul_apply, smul_eq_mul]
  have memH : ∀ y : κ → R, y ∈ Hs ↔ ∀ i, (((u⁻¹ : Rˣ)) : R) * y i ∈ O := by
    intro y; simp only [Hs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL,
      Pi.smul_apply, smul_eq_mul]
  have hLset : (L : Set (κ → R)) = Set.univ.pi (fun _ => (O : Set R)) := by
    ext y; simp [memL]
  have hLopen : IsOpen (L : Set (κ → R)) := by
    rw [hLset]; exact isOpen_set_pi Set.finite_univ (fun _ _ => hG.isOpen)
  have hLcpt : IsCompact (L : Set (κ → R)) := by
    rw [hLset]; exact isCompact_univ_pi (fun _ => hG.compact)
  have hGset : (Gs : Set (κ → R)) =
      (fun y : κ → R => ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • y) '' (L : Set (κ → R)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(((u⁻¹ * v : Rˣ)) : R) • y, hy, ?_⟩
      simp only [smul_smul, Units.inv_mul, one_smul]
    · rintro ⟨z, hz, rfl⟩
      show (((u⁻¹ * v : Rˣ)) : R) • ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • z ∈ L
      rw [smul_smul, Units.mul_inv, one_smul]; exact hz
  have hGcpt : IsCompact (Gs : Set (κ → R)) := by
    rw [hGset]; exact hLcpt.image (continuous_const_smul _)
  have hHopen : IsOpen (Hs : Set (κ → R)) :=
    hLopen.preimage (continuous_const_smul (((u⁻¹ : Rˣ)) : R))
  let H : AddSubgroup Gs := Hs.addSubgroupOf Gs
  have hHopen' : IsOpen (H : Set Gs) := hHopen.preimage continuous_subtype_val
  haveI : CompactSpace Gs := isCompact_iff_compactSpace.mp hGcpt
  haveI : Finite (Gs ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHopen'
  letI : Fintype (Gs ⧸ H) := Fintype.ofFinite _
  have hfun : (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) =
      ∑ q : Gs ⧸ H, ((Fintype.card (Gs ⧸ H) : ℂ)⁻¹) •
        schr ψ (0, ((q.out : Gs) : κ → R)) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero]
    by_cases hx : ∀ i, x i ∈ O
    · let χx : AddChar Gs ℂ :=
        { toFun := fun y => ψ (x ⬝ᵥ (y : κ → R))
          map_zero_eq_one' := by simp
          map_add_eq_mul' := by intro a b; simp [dotProduct_add, AddChar.map_add_eq_mul] }
      have hχ : ∀ h ∈ H, χx h = 1 := by
        intro h hh
        have hh' : ((h : Gs) : κ → R) ∈ Hs := AddSubgroup.mem_addSubgroupOf.mp hh
        show ψ (x ⬝ᵥ ((h : Gs) : κ → R)) = 1
        apply addChar_sum_eq_one_of_forall
        intro i _
        have h1 := (hG.ann _).mpr ((memH _).mp hh' i) (x i) (hx i)
        rwa [mul_comm] at h1
      obtain ⟨hA, hB⟩ := sum_out H χx hχ
      have hrw : ∀ q : Gs ⧸ H, (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ *
          (ψ (x ⬝ᵥ ((q.out : Gs) : κ → R)) *
            Set.indicator {x : κ → R | ∀ i, x i ∈ O} (fun _ => (1 : ℂ)) x) =
          (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ * χx q.out := by
        intro q
        simp only [Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_one]
        rfl
      rw [Finset.sum_congr rfl (fun q _ => hrw q), ← Finset.mul_sum]
      by_cases hs : ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O
      · have htriv : ∀ g, χx g = 1 := by
          intro g
          show ψ (x ⬝ᵥ ((g : Gs) : κ → R)) = 1
          apply addChar_sum_eq_one_of_forall
          intro i _
          have hg := (memG _).mp g.2 i
          have hz : ((u⁻¹ : Rˣ) : R) * ((v : R) * (g : κ → R) i) ∈ O := by
            rw [← mul_assoc, ← Units.val_mul]; exact hg
          have h1 := (hG.ann _).mpr hz _ (hs i)
          have e : (v : R) * (g : κ → R) i * (((v⁻¹ : Rˣ) : R) * x i) = x i * (g : κ → R) i := by
            rw [mul_comm (v : R) ((g : κ → R) i), mul_assoc, Units.mul_inv_cancel_left, mul_comm]
          rwa [e] at h1
        rw [hA htriv, Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
        exact (inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm
      · have hnt : ¬ ∀ g, χx g = 1 := by
          push_neg at hs
          obtain ⟨i, hi⟩ := hs
          have hz : ¬ ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) ∈ O := by
            have e : ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) = ((v⁻¹ : Rˣ) : R) * x i := by
              rw [mul_comm (((v⁻¹ : Rˣ) : R)) (u : R), mul_assoc (u : R), Units.inv_mul_cancel_left]
            rw [e]; exact hi
          rw [← hG.ann] at hz
          push_neg at hz
          obtain ⟨y, hy, hψ⟩ := hz
          intro hall
          have hmem : (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) ∈ Gs := by
            rw [memG]
            intro j
            by_cases hj : j = i
            · subst hj
              simp only [Pi.single_eq_same]
              have e : (((u⁻¹ * v : Rˣ)) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * y) = y := by
                rw [Units.val_mul, mul_assoc, ← mul_assoc (v : R), ← mul_assoc (v : R),
                  Units.mul_inv, one_mul, Units.inv_mul_cancel_left]
              rw [e]; exact hy
            · simp only [Pi.single_eq_of_ne hj, mul_zero]; exact O.zero_mem
          have h1 := hall ⟨_, hmem⟩
          apply hψ
          have e2 : x ⬝ᵥ (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) =
              ((v⁻¹ : Rˣ) : R) * (u : R) * x i * y := by
            rw [dotProduct_single]; ring
          rw [← e2]; exact h1
        rw [hB hnt, mul_zero, Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
    · have hs : ¬ ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O := by
        intro h
        apply hx
        intro i
        have := O.mul_mem hv (h i)
        rwa [Units.mul_inv_cancel_left] at this
      rw [Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      rw [Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_zero, mul_zero]
  rw [hfun]
  exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
end GlobalTheory.CompanionTheory.CosetMod
