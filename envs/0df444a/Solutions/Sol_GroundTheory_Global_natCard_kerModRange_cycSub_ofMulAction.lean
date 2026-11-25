-- Prove2me | solution 1 for GroundTheory.Global.natCard_kerModRange_cycSub_ofMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:58.429504+00:00
-- url     : https://prove2.me/submissions/53633c4a-bd7b-4681-b17b-e6f9784f7d0a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_orbitPoint_mem
import Theorems.Thm_GroundTheory_Global_orbitPoint_orbitPoint
import Theorems.Thm_GroundTheory_Global_card_stabilizer_eq_of_mem
import Theorems.Thm_GroundTheory_Global_card_stabilizer_dvd_sum
import Theorems.Thm_GroundTheory_Global_sum_smul_eq_of_support
import Theorems.Thm_GroundTheory_Global_coeff_normHom_ofMulAction
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_coeff_smul_of_mem_ker
import Theorems.Thm_GroundTheory_Global_permOfFun_mem_ker
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.coeff_permOfFun

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
namespace GroundTheory.Global
theorem _root_.solution [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ)
      (normHom (Representation.ofMulAction ℤ G X))) =
      ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by
  classical
  set K := (cycSub (Representation.ofMulAction ℤ G X) σ).ker
  let s : orbitRel.Quotient G X → ℕ := fun ω => Nat.card (stabilizer G (Quotient.out ω))
  have hs : ∀ ω, NeZero (s ω) := fun ω => ⟨Nat.card_pos.ne'⟩
  let Φ : K →+ ((ω : orbitRel.Quotient G X) → ZMod (s ω)) :=
    { toFun := fun f ω => (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) : ZMod (s ω))
      map_zero' := by
        ext ω
        simp
      map_add' := by
        intro f f'
        ext ω
        simp }
  have hΦ : ∀ (f : K) ω, Φ f ω = (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) :
      ZMod (s ω)) := fun _ _ => rfl
  have hsurj : Function.Surjective Φ := by
    intro c
    let F : X → ℤ := fun x => ((c (Quotient.mk (orbitRel G X) x)).val : ℤ)
    have hF : ∀ (g : G) x, F (g • x) = F x := by
      intro g x
      simp only [F]
      rw [Quotient.sound (orbitRel_apply.2 (mem_orbit x g))]
    refine ⟨⟨permOfFun F, permOfFun_mem_ker hF⟩, ?_⟩
    ext ω
    rw [hΦ, coeff_permOfFun]
    have hω : Quotient.mk (orbitRel G X) (Quotient.out ω) = ω := Quotient.out_eq ω
    have key : ∀ ω', ω' = ω → ((((c ω').val : ℕ) : ℤ) : ZMod (s ω)) = c ω := by
      rintro _ rfl
      rw [Int.cast_natCast]
      exact @ZMod.natCast_zmod_val _ (hs _) _
    exact key _ hω
  have hker : Φ.ker = (normHom (Representation.ofMulAction ℤ G X)).range.addSubgroupOf K := by
    ext f
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hf
      have hinv := coeff_smul_of_mem_ker hσ f.2
      have hdiv : ∀ x, (Nat.card (stabilizer G x) : ℤ) ∣ (f : MonoidAlgebra ℤ X).coeff x := by
        intro x
        have h1 := congrFun hf (Quotient.mk (orbitRel G X) x)
        rw [hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
        obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) x
        have h2 : Quotient.out (Quotient.mk (orbitRel G X) x) = g • x := hg.symm
        rw [h2, hinv] at h1
        simp only [s, h2] at h1
        rwa [card_stabilizer_eq_of_mem (mem_orbit x g)] at h1
      let H : X → ℤ := fun y =>
        if orbitPoint G y = y then (f : MonoidAlgebra ℤ X).coeff y / Nat.card (stabilizer G y)
        else 0
      have hH : ∀ y, H y ≠ 0 → orbitPoint G y = y := by
        intro y hy
        by_contra h
        exact hy (if_neg h)
      refine ⟨permOfFun H, ?_⟩
      ext p
      rw [coeff_normHom_ofMulAction]
      simp only [coeff_permOfFun]
      rw [sum_smul_eq_of_support H hH p]
      simp only [H, orbitPoint_orbitPoint, if_true]
      obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) p
      have hgp : g • p = orbitPoint G p := hg
      rw [card_stabilizer_eq_of_mem (orbitPoint_mem p), ← hgp, hinv, Int.mul_ediv_cancel' (hdiv p)]
    · rintro ⟨h, hh⟩
      funext ω
      rw [hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, ← hh, coeff_normHom_ofMulAction]
      exact card_stabilizer_dvd_sum _ _
  calc Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ) (normHom (Representation.ofMulAction ℤ G X)))
      = Nat.card (K ⧸ Φ.ker) :=
        Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hker.symm).toEquiv
    _ = Nat.card ((ω : orbitRel.Quotient G X) → ZMod (s ω)) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).toEquiv
    _ = ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by
        rw [Nat.card_pi]
        simp only [Nat.card_zmod, s]
end GroundTheory.Global
