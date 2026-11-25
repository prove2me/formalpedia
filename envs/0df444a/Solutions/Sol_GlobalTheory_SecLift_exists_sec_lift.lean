-- Prove2me | solution 1 for GlobalTheory.SecLift.exists_sec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:29.29935+00:00
-- url     : https://prove2.me/submissions/3745d68a-c296-4679-9b23-fa333a69969d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SecLift_surj_of_nil
import Theorems.Thm_GlobalTheory_SecLift_inducing_of_surj
import Theorems.Thm_GlobalTheory_SecLift_stalkMap_gr
import Theorems.Thm_GlobalTheory_SecLift_stalk_iff
import Theorems.Thm_GlobalTheory_SecLift_exists_div
import Theorems.Thm_GlobalTheory_SecLift_sec_of_refine
import Theorems.Thm_GlobalTheory_SecLift_iso_rel
import Theorems.Thm_GlobalTheory_SecLift_exists_unit
import Theorems.Thm_GlobalTheory_SecLift_sec_rel
import Theorems.Thm_GlobalTheory_SecLift_split_cocycle
import Theorems.Thm_GlobalTheory_SecLift_exists_nbhd
import Theorems.Thm_GlobalTheory_SmallExtLift_app_surj
import Theorems.Thm_GlobalTheory_SmallExtLift_cstS_comp
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cocycle
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ (N' : LB X') (w' : LB.Iso N' (N.pull β)), N'.IsLB → w'.IsGen → ∀ s' : LB.Sec N', ∃ s : LB.Sec N, (∀ z (k : (N).ι) (k' : (N').ι), (β) z ∈ (N).U k → z ∈ (N').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  intro A A₀ A' _ _ _ g₀ g' a hg₀ hg' hn hk' ha hann X X₀ X' f f₀ f' j β _ P₀ P' N N₀ w₀ hN hN₀ hw₀
    H N' w' hN' hw' s'
  have nil : ∀ x ∈ RingHom.ker g₀, IsNilpotent x := fun x hx => by
    obtain ⟨n, hn⟩ := hn
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow hx n⟩
  have sj := surj_of_nil hg₀ nil P₀
  have sβ := surj_of_nil hg' (fun x hx => nil x (by
    rw [hk'] at hx
    exact (Ideal.span_singleton_le_iff_mem _).2 ha hx)) P'
  have hS := stalk_iff hg₀ hann P₀
  let I := {q : N.ι × N₀.ι × N'.ι × X.Opens // IsAffineOpen q.2.2.2 ∧ q.2.2.2 ≤ N.U q.1 ∧
    j ⁻¹ᵁ q.2.2.2 ≤ N₀.U q.2.1 ∧ β ⁻¹ᵁ q.2.2.2 ≤ N'.U q.2.2.1}
  obtain ⟨I, V, k, k₀, k', hV, h, h₀, h', cov⟩ : ∃ (I : Type) (V : I → X.Opens) (k : I → N.ι)
      (k₀ : I → N₀.ι) (k' : I → N'.ι), (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ N.U (k i)) ∧
      (∀ i, j ⁻¹ᵁ V i ≤ N₀.U (k₀ i)) ∧ (∀ i, β ⁻¹ᵁ V i ≤ N'.U (k' i)) ∧ ∀ x, ∃ i, x ∈ V i := by
    refine ⟨I, fun q => q.1.2.2.2, fun q => q.1.1, fun q => q.1.2.1, fun q => q.1.2.2.1,
      fun q => q.2.1, fun q => q.2.2.1, fun q => q.2.2.2.1, fun q => q.2.2.2.2, fun x => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hN x
    obtain ⟨U₀, k₀, m₀, l₀⟩ := exists_nbhd hN₀ (inducing_of_surj hg₀ P₀) sj x
    obtain ⟨U', k', m', l'⟩ := exists_nbhd hN' (inducing_of_surj hg' P') sβ x
    obtain ⟨V, hV, hx, hl⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ N.U k ⊓ U₀ ⊓ U' from ⟨⟨hk, m₀⟩, m'⟩)
    exact ⟨⟨(k, k₀, k', V), hV, fun _ hy => (hl hy).1.1, fun _ hy => l₀ (hl hy).1.2,
      fun _ hy => l' (hl hy).2⟩, hx⟩
  choose ω hω using fun i => exists_unit w' (k i) (k' i) (h i) (h' i)
  choose u hu using fun i => app_surj hg' P' (hV i) ((ω i).val * rs X' (h' i) (s'.f (k' i)))
  have hu' : ∀ i (z : X') (hz : β z ∈ V i), gr (𝟙 X' ≫ β) z (V i) hz (u i) =
      (Geo.Tor.gw w' (𝟙 X') z (k i) (k' i)).val * gr (𝟙 X') z _ (h' i hz) (s'.f (k' i)) :=
    fun i z hz => by rw [← gr_app (𝟙 X') β z (V i) hz, hu, map_mul, hω, gr_res]
  have key : ∀ (l : N.ι) (l' : N'.ι) i (z : X') (hl : β z ∈ N.U l) (hl' : z ∈ N'.U l')
      (hz : β z ∈ V i), gr (𝟙 X' ≫ β) z (N.U l ⊓ N.U (k i)) ⟨hl, h i hz⟩ (N.g l (k i)).val *
        gr (𝟙 X' ≫ β) z (V i) hz (u i) =
      (Geo.Tor.gw w' (𝟙 X') z l l').val * gr (𝟙 X') z _ hl' (s'.f l') := fun l l' i z hl hl' hz => by
    rw [hu', sec_rel s' z hl' (h' i hz), ← _root_.mul_assoc, ← _root_.mul_assoc,
      iso_rel hw' z hl (h i hz) hl' (h' i hz)]
  let d : ∀ i l, Γ(X, V i ⊓ V l) := fun i l => rs X inf_le_left (u i) -
    rs X (inf_le_inf (h i) (h l)) (N.g (k i) (k l)).val * rs X inf_le_right (u l)
  have hd : ∀ i l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (hz : r z ∈ V i ⊓ V l),
      gr r z _ hz (d i l) = gr r z (V i) hz.1 (u i) -
        gr r z (N.U (k i) ⊓ N.U (k l)) ⟨h i hz.1, h l hz.2⟩ (N.g (k i) (k l)).val *
          gr r z (V l) hz.2 (u l) := fun i l Z r z hz => by
    simp only [d]
    rw [map_sub, map_mul, gr_res, gr_res, gr_res]
  choose φ hφ using fun i l => exists_div (a := a) (f := f) (j := j) (fun y e => (hS y e).1)
    (V i ⊓ V l) (d i l) (fun W hle hW => by
      have := mem_of_app_eq_zero hg' P' hW (rs X hle (d i l)) (gr_ext fun z hz => by
        rw [gr_app, gr_res, hd, map_zero, key (k i) (k' i) l z (h i (hle hz).1) (h' i (hle hz).1)
          (hle hz).2, hu' i z (hle hz).1, sub_self])
      rwa [hk', Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this)
  obtain ⟨ψ, hψ⟩ := split_cocycle hw₀ H V cov k k₀ h h₀ φ (fun i l m y hi hl hm => by
    obtain ⟨e₁, p₁, q₁⟩ := hφ i l y ⟨hi, hl⟩
    obtain ⟨e₂, p₂, q₂⟩ := hφ l m y ⟨hl, hm⟩
    obtain ⟨e₃, p₃, q₃⟩ := hφ i m y ⟨hi, hm⟩
    rw [← q₁, ← q₂, ← q₃, ← stalkMap_gr, ← map_mul, ← map_add, ← sub_eq_zero, ← map_sub, ← hS]
    rw [hd] at p₁ p₂ p₃
    have c := gr_cocycle hN (𝟙 X) (j y) (h i hi) (h l hl) (h m hm)
    linear_combination p₃ - p₁ - gr (𝟙 X) (j y) (N.U (k i) ⊓ N.U (k l)) ⟨h i hi, h l hl⟩
      (N.g (k i) (k l)).val * p₂ - gr (𝟙 X) (j y) (V m) hm (u m) * c)
  choose v hv using fun i => app_surj hg₀ P₀ (hV i) (ψ i)
  obtain ⟨s, hs⟩ := sec_of_refine hN V cov k h (fun i => u i - cst f (V i) a * v i)
    (fun i l x hi hl => by
      obtain ⟨y, rfl⟩ := sj x
      obtain ⟨e, p, q⟩ := hφ i l y ⟨hi, hl⟩
      have c := hψ i l y hi hl
      rw [← q, ← hv, ← hv, gr_app, gr_app, ← stalkMap_gr, ← stalkMap_gr, ← stalkMap_gr, ← map_mul,
        ← map_sub, ← sub_eq_zero, ← map_sub, ← hS] at c
      rw [hd] at p
      rw [map_sub, map_sub, map_mul, map_mul, gr_cst, gr_cst]
      linear_combination p + c)
  refine ⟨s, fun z l l' hl hl' => ?_⟩
  obtain ⟨i, hi⟩ := cov (β z)
  have c := hs l i _ (𝟙 X' ≫ β) z hl hi
  have ha' : g' a = 0 := by
    rw [← RingHom.mem_ker, hk']
    exact Ideal.mem_span_singleton_self a
  rw [map_sub, map_mul, gr_cst, Category.assoc, P'.w, ← Category.assoc, cstS_comp, ha', map_zero,
    zero_mul, sub_zero, key l l' i z hl hl' hi] at c
  rw [gs_eq β z _ hl, gs_eq (𝟙 X') z _ hl']
  exact c
end GlobalTheory.SecLift
