-- Prove2me | solution 1 for MasulloGRH.adelicSchwartz_range_eval_eq_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:33:53.490945+00:00
-- url     : https://prove2.me/submissions/fa5b4686-61e7-4690-b12a-15269930e969

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_MasulloGRH_exists_small_good_subgroups
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology

open NumberField IsDedekindDomain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Sol_MasulloGRH_adelicSchwartz_range_eval_eq_schwartzBruhat

open MasulloGRH Topology Filter Set

section Elem
variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- The subset `ℝ^m × 𝕋^n × {0} × {0}` of `ℝ^m × 𝕋^n × ℤ^r × F`. -/
def compSet (m n r s : ℕ) (d : Fin s → ℕ) : Set (Multiplicative (ElemGroup m n r s d)) :=
  {e | (Multiplicative.toAdd e).2.2 = 0}

theorem isOpen_compSet : IsOpen (compSet m n r s d) := by
  have hc : Continuous fun e : Multiplicative (ElemGroup m n r s d) =>
      (Multiplicative.toAdd e).2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_toAdd)
  exact (isOpen_discrete ({0} : Set ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))))).preimage hc

theorem isPreconnected_compSet : IsPreconnected (compSet m n r s d) := by
  let φ : (Fin m → ℝ) × (Fin n → ℝ) → Multiplicative (ElemGroup m n r s d) :=
    fun p => Multiplicative.ofAdd (p.1, fun j => ((p.2 j : ℝ) : UnitAddCircle), 0, 0)
  have hφ : Continuous φ := by
    refine continuous_ofAdd.comp ?_
    refine continuous_fst.prodMk (Continuous.prodMk ?_ continuous_const)
    exact continuous_pi fun j =>
      (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply j).comp continuous_snd)
  have hrange : Set.range φ = compSet m n r s d := by
    ext e
    constructor
    · rintro ⟨p, rfl⟩; rfl
    · intro he
      have ht : ∀ j, ∃ t : ℝ, ((t : ℝ) : UnitAddCircle) = (Multiplicative.toAdd e).2.1 j :=
        fun j => QuotientAddGroup.mk_surjective _
      choose t ht using ht
      refine ⟨((Multiplicative.toAdd e).1, t), ?_⟩
      show Multiplicative.ofAdd _ = e
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      have he' : (Multiplicative.toAdd e).2.2 = 0 := he
      ext1
      · rfl
      ext1
      · exact funext ht
      · exact he'.symm
  rw [← hrange]
  exact isPreconnected_range hφ

theorem circle_norm_two_nsmul (z : UnitAddCircle) (hz : ‖z‖ < 1 / 4) :
    ‖(2 : ℕ) • z‖ = 2 * ‖z‖ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hround : (((round x : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨round x, by simp⟩
  have hyx : (((x - round x : ℝ)) : UnitAddCircle) = (QuotientAddGroup.mk x : UnitAddCircle) := by
    rw [AddCircle.coe_sub, hround, sub_zero]
  have hn : ‖(QuotientAddGroup.mk x : UnitAddCircle)‖ = |x - round x| := UnitAddCircle.norm_eq
  rw [← hyx] at hz ⊢
  rw [← AddCircle.coe_nsmul]
  have h1 : ‖((x - round x : ℝ) : UnitAddCircle)‖ = |x - round x| := by rw [hyx, hn]
  rw [h1] at hz ⊢
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2]
  · rw [nsmul_eq_mul, abs_mul]; norm_num
  · rw [nsmul_eq_mul, abs_mul]; norm_num; linarith

theorem circle_eq_zero (z : UnitAddCircle) (h : ∀ N : ℕ, ‖N • z‖ < 1 / 4) : z = 0 := by
  have key : ∀ j : ℕ, ‖(2 ^ j : ℕ) • z‖ = 2 ^ j * ‖z‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (2 ^ (j + 1) : ℕ) • z = (2 : ℕ) • ((2 ^ j : ℕ) • z) := by
        rw [← mul_smul, pow_succ, mul_comm]
      rw [e, circle_norm_two_nsmul _ (h _), ih, pow_succ]; ring
  by_contra hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (4 * ‖z‖)) (by norm_num : (1 : ℝ) < 2)
  have h2 := h (2 ^ j)
  rw [key] at h2
  rw [div_lt_iff₀ (by positivity)] at hj
  nlinarith

theorem real_eq_zero {m : ℕ} (y : Fin m → ℝ) (h : ∀ N : ℕ, ‖N • y‖ < 1) : y = 0 := by
  by_contra hy
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖y‖)
  have h2 := h N
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at h2
  rw [div_lt_iff₀ hpos] at hN
  linarith

/-- A neighbourhood of `0` in `ℝ^m × 𝕋^n × ℤ^r × F` containing no nontrivial subgroup. -/
def nssSet (m n r s : ℕ) (d : Fin s → ℕ) : Set (ElemGroup m n r s d) :=
  {e | ‖e.1‖ < 1 ∧ (∀ j, ‖e.2.1 j‖ < 1 / 4) ∧ e.2.2 = 0}

theorem isOpen_nssSet : IsOpen (nssSet m n r s d) := by
  have h1 : IsOpen {e : ElemGroup m n r s d | ‖e.1‖ < 1} :=
    isOpen_lt continuous_fst.norm continuous_const
  have h2 : IsOpen {e : ElemGroup m n r s d | ∀ j, ‖e.2.1 j‖ < 1 / 4} := by
    have : {e : ElemGroup m n r s d | ∀ j, ‖e.2.1 j‖ < 1 / 4} =
        ⋂ j, {e : ElemGroup m n r s d | ‖e.2.1 j‖ < 1 / 4} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm
        continuous_const
  have h3 : IsOpen {e : ElemGroup m n r s d | e.2.2 = 0} :=
    (isOpen_discrete ({0} : Set ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))))).preimage
      (continuous_snd.comp continuous_snd)
  exact h1.inter (h2.inter h3)

theorem zero_mem_nssSet : (0 : ElemGroup m n r s d) ∈ nssSet m n r s d :=
  ⟨by simp, fun j => by simp, rfl⟩

theorem nss (c : ElemGroup m n r s d) (h : ∀ N : ℕ, N • c ∈ nssSet m n r s d) : c = 0 := by
  have h1 : c.1 = 0 := real_eq_zero _ fun N => (h N).1
  have h2 : c.2.1 = 0 := funext fun j => circle_eq_zero _ fun N => (h N).2.1 j
  have h3 : c.2.2 = 0 := by simpa using (h 1).2.2
  exact Prod.ext h1 (Prod.ext h2 h3)

end Elem


section Core

variable {X H : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

/-- `x ↦ (x, 0)`. -/
def iX (x : X) : Multiplicative (X × H) := Multiplicative.ofAdd (x, 0)
/-- `h ↦ (0, h)`. -/
def iH (h : H) : Multiplicative (X × H) := Multiplicative.ofAdd (0, h)

theorem iX_add (x x' : X) : (iX (x + x') : Multiplicative (X × H)) = iX x * iX x' := by
  apply Multiplicative.toAdd.injective; simp [iX]

theorem iH_add (h h' : H) : (iH (h + h') : Multiplicative (X × H)) = iH h * iH h' := by
  apply Multiplicative.toAdd.injective; simp [iH]

theorem iX_zero : (iX (0 : X) : Multiplicative (X × H)) = 1 := rfl
theorem iH_zero : (iH (0 : H) : Multiplicative (X × H)) = 1 := rfl

theorem iX_nsmul (N : ℕ) (x : X) : (iX (N • x) : Multiplicative (X × H)) = iX x ^ N := by
  apply Multiplicative.toAdd.injective; simp [iX]

theorem iH_nsmul (N : ℕ) (h : H) : (iH (N • h) : Multiplicative (X × H)) = iH h ^ N := by
  apply Multiplicative.toAdd.injective; simp [iH]

theorem decomp (y : Multiplicative (X × H)) :
    y = iX (Multiplicative.toAdd y).1 * iH (Multiplicative.toAdd y).2 := by
  apply Multiplicative.toAdd.injective; simp [iX, iH]

theorem continuous_iX : Continuous (iX : X → Multiplicative (X × H)) :=
  continuous_ofAdd.comp (continuous_id.prodMk continuous_const)

theorem continuous_iH : Continuous (iH : H → Multiplicative (X × H)) :=
  continuous_ofAdd.comp (continuous_const.prodMk continuous_id)

theorem iX_mem [ConnectedSpace X] {Γ : Subgroup (Multiplicative (X × H))}
    (hΓ : IsOpen (Γ : Set (Multiplicative (X × H)))) (x : X) : iX x ∈ Γ := by
  let A : AddSubgroup X :=
    { carrier := {x | (iX x : Multiplicative (X × H)) ∈ Γ}
      add_mem' := fun {a b} ha hb => by
        show iX (a + b) ∈ Γ
        rw [iX_add]; exact Γ.mul_mem ha hb
      zero_mem' := by show iX 0 ∈ Γ; rw [iX_zero]; exact Γ.one_mem
      neg_mem' := fun {a} ha => by
        show iX (-a) ∈ Γ
        have : (iX (-a) : Multiplicative (X × H)) = (iX a)⁻¹ := by
          apply Multiplicative.toAdd.injective; simp [iX]
        rw [this]; exact Γ.inv_mem ha }
  have hAo : IsOpen (A : Set X) := hΓ.preimage continuous_iX
  have hAc : IsClosed (A : Set X) := AddSubgroup.isClosed_of_isOpen A hAo
  have : (A : Set X) = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨0, A.zero_mem⟩
  have hx : x ∈ (A : Set X) := this ▸ mem_univ x
  exact hx

/-- The finite part `Γ_f = {h | (0, h) ∈ Γ}`. -/
def Gf (Γ : Subgroup (Multiplicative (X × H))) : AddSubgroup H where
  carrier := {h | (iH h : Multiplicative (X × H)) ∈ Γ}
  add_mem' := fun {a b} ha hb => by
    show iH (a + b) ∈ Γ
    rw [iH_add]; exact Γ.mul_mem ha hb
  zero_mem' := by show iH 0 ∈ Γ; rw [iH_zero]; exact Γ.one_mem
  neg_mem' := fun {a} ha => by
    show iH (-a) ∈ Γ
    have : (iH (-a) : Multiplicative (X × H)) = (iH a)⁻¹ := by
      apply Multiplicative.toAdd.injective; simp [iH]
    rw [this]; exact Γ.inv_mem ha

theorem mem_Gf_iff {Γ : Subgroup (Multiplicative (X × H))} {h : H} :
    h ∈ Gf Γ ↔ (iH h : Multiplicative (X × H)) ∈ Γ := Iff.rfl

theorem mem_iff_snd_mem_Gf [ConnectedSpace X] {Γ : Subgroup (Multiplicative (X × H))}
    (hΓ : IsOpen (Γ : Set (Multiplicative (X × H)))) (y : Multiplicative (X × H)) :
    y ∈ Γ ↔ (Multiplicative.toAdd y).2 ∈ Gf Γ := by
  constructor
  · intro hy
    have h2 : (iX (Multiplicative.toAdd y).1)⁻¹ * y ∈ Γ := Γ.mul_mem (Γ.inv_mem (iX_mem hΓ _)) hy
    have e : (iH (Multiplicative.toAdd y).2 : Multiplicative (X × H)) =
        (iX (Multiplicative.toAdd y).1)⁻¹ * y := by
      rw [eq_inv_mul_iff_mul_eq]; exact (decomp y).symm
    show iH _ ∈ Γ
    rw [e]; exact h2
  · intro hy
    rw [decomp y]; exact Γ.mul_mem (iX_mem hΓ _) hy

theorem isOpen_Gf {Γ : Subgroup (Multiplicative (X × H))}
    (hΓ : IsOpen (Γ : Set (Multiplicative (X × H)))) : IsOpen (Gf Γ : Set H) :=
  hΓ.preimage continuous_iH

theorem fst_eq_zero_of_mem_compact {k : Subgroup (Multiplicative (X × H))}
    (hk : IsCompact (k : Set (Multiplicative (X × H))))
    (hXb : ∀ S : Set X, IsCompact S → ∀ x : X, (∀ N : ℕ, N • x ∈ S) → x = 0)
    {y : Multiplicative (X × H)} (hy : y ∈ k) : (Multiplicative.toAdd y).1 = 0 :=
  hXb _ (hk.image (continuous_fst.comp continuous_toAdd)) _ fun N =>
    ⟨y ^ N, k.pow_mem hy N, by simp⟩

theorem isCompact_Gf [ConnectedSpace X] {Γ : Subgroup (Multiplicative (X × H))}
    (hΓ : IsOpen (Γ : Set (Multiplicative (X × H)))) (hcg : IsCompactlyGeneratedSubgroup Γ)
    (hHcpt : ∀ C : Set H, IsCompact C → ∃ V : AddSubgroup H, IsCompact (V : Set H) ∧ C ⊆ V) :
    IsCompact (Gf Γ : Set H) := by
  obtain ⟨U, hUc, -, -, hUgen⟩ := hcg
  obtain ⟨C, hCc, hUC⟩ := hHcpt ((fun y => (Multiplicative.toAdd y).2) '' U)
    (hUc.image (continuous_snd.comp continuous_toAdd))
  let ΓC : Subgroup (Multiplicative (X × H)) :=
    { carrier := {y | (Multiplicative.toAdd y).2 ∈ C}
      mul_mem' := fun {a b} ha hb => C.add_mem ha hb
      one_mem' := C.zero_mem
      inv_mem' := fun {a} ha => C.neg_mem ha }
  have hle : Γ ≤ ΓC := by
    rw [← hUgen]; exact (Subgroup.closure_le ΓC).2 fun y hy => hUC ⟨y, hy, rfl⟩
  have hsub : (Gf Γ : Set H) ⊆ C := fun h hh => hle hh
  exact hCc.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_Gf hΓ)) hsub

theorem exists_nsmul_mem {Γf Wf : AddSubgroup H} (hc : IsCompact (Γf : Set H))
    (ho : IsOpen (Wf : Set H)) {h : H} (hh : h ∈ Γf) : ∃ N : ℕ, N ≠ 0 ∧ N • h ∈ Wf := by
  have hcov : (Γf : Set H) ⊆ ⋃ c : Γf, (fun y => y - (c : H)) ⁻¹' (Wf : Set H) :=
    fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [Wf.zero_mem]⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _
    (fun c => ho.preimage (continuous_id.sub continuous_const)) hcov
  have hmem : ∀ j : ℕ, ∃ c ∈ t, j • h - (c : H) ∈ Wf := fun j => by
    have := ht (Γf.nsmul_mem hh j)
    simpa using this
  choose c hct hc using hmem
  let f : ℕ → t := fun j => ⟨c j, hct j⟩
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hcij : c i = c j := congrArg Subtype.val hfij
  have hdiff : i • h - j • h ∈ Wf := by
    have := Wf.sub_mem (hc i) (hc j); rwa [hcij, sub_sub_sub_cancel_right] at this
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, by omega, ?_⟩
    have e : (j - i) • h = j • h - i • h := by
      rw [eq_sub_iff_add_eq, ← add_nsmul, Nat.sub_add_cancel hlt.le]
    rw [e]
    have := Wf.neg_mem hdiff; rwa [neg_sub] at this
  · refine ⟨i - j, by omega, ?_⟩
    have e : (i - j) • h = i • h - j • h := by
      rw [eq_sub_iff_add_eq, ← add_nsmul, Nat.sub_add_cancel hlt.le]
    rw [e]; exact hdiff

variable {Γ k : Subgroup (Multiplicative (X × H))} {m n r s : ℕ} {d : Fin s → ℕ}

theorem exists_Wf (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : IsElemPresentation Γ k π)
    (hΓ : IsOpen (Γ : Set (Multiplicative (X × H))))
    (hHbasis : ∀ W ∈ 𝓝 (0 : H), ∃ V : AddSubgroup H, IsOpen (V : Set H) ∧ (V : Set H) ⊆ W) :
    ∃ Wf : AddSubgroup H, IsOpen (Wf : Set H) ∧ Wf ≤ Gf Γ ∧
      ∀ w ∈ Wf, (iH w : Multiplicative (X × H)) ∈ k := by
  let O : Set (Multiplicative (X × H)) :=
    Subtype.val '' {y : Γ | Multiplicative.toAdd (π y) ∈ nssSet m n r s d}
  have hOo : IsOpen O := hΓ.isOpenMap_subtype_val _
    (isOpen_nssSet.preimage (continuous_toAdd.comp hπ.2.1))
  have h0 : (0 : H) ∈ (iH : H → Multiplicative (X × H)) ⁻¹' O := by
    refine ⟨1, ?_, rfl⟩
    show Multiplicative.toAdd (π 1) ∈ nssSet m n r s d
    rw [map_one]; exact zero_mem_nssSet
  obtain ⟨V, hVo, hVW⟩ := hHbasis _ ((hOo.preimage continuous_iH).mem_nhds h0)
  have hVΓ : ∀ w ∈ V, ∃ hw : (iH w : Multiplicative (X × H)) ∈ Γ,
      Multiplicative.toAdd (π ⟨iH w, hw⟩) ∈ nssSet m n r s d := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hVW hw
    have hw' : (iH w : Multiplicative (X × H)) ∈ Γ := hyw ▸ y.2
    refine ⟨hw', ?_⟩
    have : (⟨iH w, hw'⟩ : Γ) = y := Subtype.ext hyw.symm
    rw [this]; exact hy
  refine ⟨V, hVo, fun w hw => (hVΓ w hw).1, fun w hw => ?_⟩
  obtain ⟨hwΓ, -⟩ := hVΓ w hw
  show ((⟨iH w, hwΓ⟩ : Γ) : Multiplicative (X × H)) ∈ k
  rw [← hπ.2.2.2.2 ⟨iH w, hwΓ⟩]
  have hc : Multiplicative.toAdd (π ⟨iH w, hwΓ⟩) = 0 := nss _ fun N => by
    obtain ⟨hN, hNmem⟩ := hVΓ (N • w) (V.nsmul_mem hw N)
    have e : (⟨iH (N • w), hN⟩ : Γ) = ⟨iH w, hwΓ⟩ ^ N := Subtype.ext (by simp [iH_nsmul])
    rw [e, map_pow, toAdd_pow] at hNmem; exact hNmem
  exact Multiplicative.toAdd.injective hc

theorem core [ConnectedSpace X] (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hXtf : ∀ x : X, (2 : ℕ) • x = 0 → x = 0)
    (hXb : ∀ S : Set X, IsCompact S → ∀ x : X, (∀ N : ℕ, N • x ∈ S) → x = 0)
    (hHbasis : ∀ W ∈ 𝓝 (0 : H), ∃ V : AddSubgroup H, IsOpen (V : Set H) ∧ (V : Set H) ⊆ W)
    (hk : IsCompact (k : Set (Multiplicative (X × H))))
    (hΓ : IsOpen (Γ : Set (Multiplicative (X × H)))) (hΓc : IsCompact (Gf Γ : Set H))
    (hπ : IsElemPresentation Γ k π) :
    n = 0 ∧ r = 0 ∧ ∃ (L : X →+ (Fin m → ℝ)) (b : H → ((i : Fin s) → ZMod (d i)))
      (Wf : AddSubgroup H),
      Continuous L ∧ Function.Bijective L ∧ IsOpen (Wf : Set H) ∧ Wf ≤ Gf Γ ∧
      (∀ y (hy : y ∈ Γ), (Multiplicative.toAdd (π ⟨y, hy⟩)).1 = L (Multiplicative.toAdd y).1 ∧
        (Multiplicative.toAdd (π ⟨y, hy⟩)).2.2.2 = b (Multiplicative.toAdd y).2) ∧
      (∀ h w, w ∈ Wf → b (h + w) = b h) := by
  classical
  obtain ⟨Wf, hWo, hWΓ, hWk⟩ := exists_Wf π hπ hΓ hHbasis
  have hker := hπ.2.2.2.2
  let αf : X → Multiplicative (ElemGroup m n r s d) := fun x => π ⟨iX x, iX_mem hΓ x⟩
  have hα_add : ∀ x x', αf (x + x') = αf x * αf x' := fun x x' => by
    simp only [αf]; rw [← map_mul]; congr 1; exact Subtype.ext (iX_add x x')
  have hα0 : αf 0 = 1 := by
    simp only [αf]; rw [← map_one π]; congr 1
  have hα_cont : Continuous αf := hπ.2.1.comp (continuous_iX.subtype_mk _)
  have hα_nsmul : ∀ (N : ℕ) x, αf (N • x) = αf x ^ N := by
    intro N x
    induction N with
    | zero => simp [hα0]
    | succ N ih => rw [succ_nsmul, hα_add, ih, pow_succ]
  have hβ_add : ∀ h h' (hh : h ∈ Gf Γ) (hh' : h' ∈ Gf Γ),
      π ⟨iH (h + h'), (Gf Γ).add_mem hh hh'⟩ = π ⟨iH h, hh⟩ * π ⟨iH h', hh'⟩ := by
    intro h h' hh hh'; rw [← map_mul]; congr 1; exact Subtype.ext (iH_add _ _)
  have hβW : ∀ w (hw : w ∈ Gf Γ), w ∈ Wf → π ⟨iH w, hw⟩ = 1 :=
    fun w hw hwW => (hker _).2 (hWk w hwW)
  have hsplit : ∀ y (hy : y ∈ Γ), π ⟨y, hy⟩ =
      αf (Multiplicative.toAdd y).1 * π ⟨iH (Multiplicative.toAdd y).2,
        (mem_iff_snd_mem_Gf hΓ y).1 hy⟩ := by
    intro y hy; rw [← map_mul]; congr 1; exact Subtype.ext (decomp y)
  have hα_comp : ∀ x, (Multiplicative.toAdd (αf x)).2.2 = 0 := by
    intro x
    have hc : Continuous fun x => (Multiplicative.toAdd (αf x)).2.2 :=
      continuous_snd.comp (continuous_snd.comp (continuous_toAdd.comp hα_cont))
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace X) hc (x := x) (y := 0)
    rw [this, hα0]; rfl
  have hα_open : IsOpen (range αf) := by
    have : range αf = π '' {y : Γ | (Multiplicative.toAdd (y : Multiplicative (X × H))).2 ∈ Wf} := by
      ext e; constructor
      · rintro ⟨x, rfl⟩
        exact ⟨⟨iX x, iX_mem hΓ x⟩, show (0 : H) ∈ Wf from Wf.zero_mem, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨(Multiplicative.toAdd (y : Multiplicative (X × H))).1, ?_⟩
        have := hsplit y.1 y.2
        rw [hβW _ _ hy, mul_one] at this
        exact this.symm
    rw [this]
    exact hπ.2.2.1 _ (hWo.preimage (continuous_snd.comp (continuous_toAdd.comp continuous_subtype_val)))
  let P : Subgroup (Multiplicative (ElemGroup m n r s d)) :=
    { carrier := range αf
      mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨x', rfl⟩; exact ⟨x + x', hα_add x x'⟩
      one_mem' := ⟨0, hα0⟩
      inv_mem' := by
        rintro _ ⟨x, rfl⟩
        refine ⟨-x, ?_⟩
        have := hα_add (-x) x
        rw [neg_add_cancel, hα0] at this
        exact eq_inv_of_mul_eq_one_left this.symm }
  have hPo : IsOpen (P : Set (Multiplicative (ElemGroup m n r s d))) := hα_open
  have hcomp_sub : compSet m n r s d ⊆ range αf :=
    isPreconnected_compSet.subset_isClopen ⟨Subgroup.isClosed_of_isOpen P hPo, hPo⟩
      ⟨1, rfl, P.one_mem⟩
  have hα_inj : ∀ x, αf x = 1 → x = 0 := fun x hx =>
    fst_eq_zero_of_mem_compact hk hXb ((hker _).1 hx)
  have hn : n = 0 := by
    by_contra hn
    let e : Multiplicative (ElemGroup m n r s d) :=
      Multiplicative.ofAdd (0, fun _ => (((1 : ℝ) / 2 : ℝ) : UnitAddCircle), 0)
    obtain ⟨x, hx⟩ := hcomp_sub (show e ∈ compSet m n r s d from rfl)
    have hhalf : (2 : ℕ) • ((((1 : ℝ) / 2 : ℝ)) : UnitAddCircle) = 0 := by
      rw [← AddCircle.coe_nsmul]; norm_num
    have h2 : αf ((2 : ℕ) • x) = 1 := by
      rw [hα_nsmul, hx]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow]
      simp only [e, toAdd_ofAdd, toAdd_one]
      ext1
      · simp
      ext1
      · funext j; exact hhalf
      · simp
    have hx0 : x = 0 := hXtf x (hα_inj _ h2)
    have he1 : e = 1 := by rw [← hx, hx0, hα0]
    have h3 := congrArg (fun e : Multiplicative (ElemGroup m n r s d) =>
      (Multiplicative.toAdd e).2.1 ⟨0, Nat.pos_of_ne_zero hn⟩) he1
    simp only [e, toAdd_ofAdd, toAdd_one] at h3
    have h4 := AddCircle.norm_half_period_eq (p := (1 : ℝ))
    rw [h3] at h4
    simp at h4
  have hβtor : ∀ h (hh : h ∈ Gf Γ), (Multiplicative.toAdd (π ⟨iH h, hh⟩)).1 = 0 ∧
      (Multiplicative.toAdd (π ⟨iH h, hh⟩)).2.2.1 = 0 := by
    intro h hh
    obtain ⟨N, hN0, hNW⟩ := exists_nsmul_mem hΓc hWo hh
    have hpow : π ⟨iH h, hh⟩ ^ N = 1 := by
      rw [← map_pow, ← hβW (N • h) ((Gf Γ).nsmul_mem hh N) hNW]
      congr 1; exact Subtype.ext (iH_nsmul N h).symm
    have hz : N • Multiplicative.toAdd (π ⟨iH h, hh⟩) = 0 := by rw [← toAdd_pow, hpow]; rfl
    constructor
    · have h1 : N • (Multiplicative.toAdd (π ⟨iH h, hh⟩)).1 = 0 := congrArg Prod.fst hz
      rw [← Nat.cast_smul_eq_nsmul ℝ] at h1
      exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hN0)
    · funext i
      have h1 : N • (Multiplicative.toAdd (π ⟨iH h, hh⟩)).2.2.1 i = 0 :=
        congrFun (congrArg (fun c => c.2.2.1) hz) i
      rw [nsmul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hN0)
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨y, hy⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd ((0, 0, fun _ => 1, 0) : ElemGroup m n r s d))
    have h1 : (Multiplicative.toAdd (π y)).2.2.1 = 0 := by
      rw [show y = ⟨y.1, y.2⟩ from rfl, hsplit]
      simp only [toAdd_mul, Prod.snd_add, Prod.fst_add]
      rw [(hβtor _ _).2, add_zero]
      exact congrArg Prod.fst (hα_comp _)
    rw [hy] at h1
    have := congrFun h1 ⟨0, Nat.pos_of_ne_zero hr⟩
    simp at this
  subst hn; subst hr
  let L : X →+ (Fin m → ℝ) :=
    { toFun := fun x => (Multiplicative.toAdd (αf x)).1
      map_zero' := by simp only [hα0]; rfl
      map_add' := fun x x' => by simp only [hα_add, toAdd_mul, Prod.fst_add] }
  let b : H → ((i : Fin s) → ZMod (d i)) := fun h =>
    if hh : h ∈ Gf Γ then (Multiplicative.toAdd (π ⟨iH h, hh⟩)).2.2.2 else 0
  refine ⟨rfl, rfl, L, b, Wf, ?_, ⟨?_, ?_⟩, hWo, hWΓ, ?_, ?_⟩
  · exact continuous_fst.comp (continuous_toAdd.comp hα_cont)
  · intro x x' hxx'
    have hsub : αf (x - x') = 1 := by
      apply Multiplicative.toAdd.injective
      have h1 : (Multiplicative.toAdd (αf (x - x'))).1 = 0 := by
        have := L.map_sub x x'
        rw [hxx', sub_self] at this
        exact this
      ext1
      · exact h1
      ext1
      · exact Subsingleton.elim _ _
      · exact hα_comp _
    exact sub_eq_zero.1 (hα_inj _ hsub)
  · intro yv
    obtain ⟨x, hx⟩ := hcomp_sub
      (show Multiplicative.ofAdd ((yv, 0, 0) : ElemGroup m 0 0 s d) ∈ compSet m 0 0 s d from rfl)
    exact ⟨x, by show (Multiplicative.toAdd (αf x)).1 = yv; rw [hx]; rfl⟩
  · intro y hy
    rw [hsplit y hy]
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    refine ⟨?_, ?_⟩
    · rw [(hβtor _ _).1, add_zero]; rfl
    · rw [show (Multiplicative.toAdd (αf (Multiplicative.toAdd y).1)).2.2.2 = 0 from
        congrArg Prod.snd (hα_comp _), zero_add]
      simp only [b, dif_pos ((mem_iff_snd_mem_Gf hΓ y).1 hy)]
  · intro h w hw
    have hwΓ := hWΓ hw
    by_cases hh : h ∈ Gf Γ
    · have hhw : h + w ∈ Gf Γ := (Gf Γ).add_mem hh hwΓ
      simp only [b, dif_pos hh, dif_pos hhw]
      rw [hβ_add h w hh hwΓ, hβW w hwΓ hw, mul_one]
    · have hhw : h + w ∉ Gf Γ := fun h' => hh (by simpa using (Gf Γ).sub_mem h' hwΓ)
      simp only [b, dif_neg hh, dif_neg hhw]

end Core

section Schwartz
open scoped SchwartzMap

variable {m s : ℕ} {d : Fin s → ℕ}

theorem norm_PSp (xt : (Fin m → ℝ) × (Fin 0 → ℝ)) : ‖xt‖ = ‖xt.1‖ := by
  rw [Prod.norm_def, Subsingleton.elim xt.2 0, norm_zero]; exact max_eq_left (norm_nonneg _)

/-- The Schwartz map `x ↦ g(x, b)` attached to a rapidly decreasing `g` on `ℝ^m × F`. -/
def schwartzOfRapid {g : ElemGroup m 0 0 s d → ℂ} (hg : IsRapidDecay g)
    (b : (i : Fin s) → ZMod (d i)) : 𝓢((Fin m → ℝ) × (Fin 0 → ℝ), ℂ) where
  toFun := elemLift g 0 b
  smooth' := hg.1 0 b
  decay' := fun k n => by
    obtain ⟨C, hC⟩ := hg.2 k 0 n
    refine ⟨C, fun x => ?_⟩
    have := hC 0 b x
    rw [pow_zero, one_mul] at this
    rw [norm_PSp]; exact this

theorem schwartzOfRapid_apply {g : ElemGroup m 0 0 s d → ℂ} (hg : IsRapidDecay g)
    (b : (i : Fin s) → ZMod (d i)) (x : (Fin m → ℝ) × (Fin 0 → ℝ)) :
    schwartzOfRapid hg b x = elemLift g 0 b x := rfl

theorem isRapidDecay_of_schwartz (Φ : 𝓢((Fin m → ℝ) × (Fin 0 → ℝ), ℂ))
    (c : ((i : Fin s) → ZMod (d i)) → ℂ) (M : ℝ) (hM : ∀ b, ‖c b‖ ≤ M) :
    IsRapidDecay (fun e : ElemGroup m 0 0 s d => Φ (e.1, 0) * c e.2.2.2) := by
  have hlift : ∀ a b, elemLift (fun e : ElemGroup m 0 0 s d => Φ (e.1, 0) * c e.2.2.2) a b =
      ⇑(c b • Φ) := by
    intro a b; funext xt
    simp only [elemLift, SchwartzMap.smul_apply, smul_eq_mul]
    rw [show ((xt.1, 0) : (Fin m → ℝ) × (Fin 0 → ℝ)) = xt from
      Prod.ext rfl (Subsingleton.elim _ _), mul_comm]
  refine ⟨fun a b => by rw [hlift]; exact (c b • Φ).smooth ⊤,
    fun i j k => ⟨max M 0 * SchwartzMap.seminorm ℂ i k Φ, fun a b xt => ?_⟩⟩
  rw [hlift]
  have ha : ‖a‖ ^ j ≤ 1 := by
    rw [Subsingleton.elim a 0, norm_zero]; exact pow_le_one₀ le_rfl zero_le_one
  have h1 : ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (⇑(c b • Φ)) xt‖ ≤
      SchwartzMap.seminorm ℂ i k (c b • Φ) := by
    rw [← norm_PSp]; exact SchwartzMap.le_seminorm ℂ i k _ xt
  have h2 : SchwartzMap.seminorm ℂ i k (c b • Φ) ≤ max M 0 * SchwartzMap.seminorm ℂ i k Φ := by
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_right ((hM b).trans (le_max_left _ _)) (apply_nonneg _ _)
  have h0 : 0 ≤ ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (⇑(c b • Φ)) xt‖ := by positivity
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (⇑(c b • Φ)) xt‖
      = ‖a‖ ^ j * (‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (⇑(c b • Φ)) xt‖) := by ring
    _ ≤ 1 * (max M 0 * SchwartzMap.seminorm ℂ i k Φ) :=
        mul_le_mul ha (h1.trans h2) h0 zero_le_one
    _ = _ := one_mul _

end Schwartz

section Adele

variable (F : Type*) [Field F] [NumberField F]
open scoped RestrictedProduct

/-- The finite adeles as a restricted product. -/
abbrev FinAd : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]

/-- The additive group of the finite adeles, written multiplicatively. -/
abbrev GA : Type _ := Multiplicative (FiniteAdeleRing (𝓞 F) F)

theorem t2_GA : T2Space (GA F) := inferInstanceAs (T2Space (FinAd F))

theorem td_GA : TotallyDisconnectedSpace (GA F) := by
  have hinj : Function.Injective
      (fun x : FinAd F => (x : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)) :=
    fun x y hxy => Subtype.ext hxy
  have : TotallyDisconnectedSpace (FinAd F) :=
    ⟨isTotallyDisconnected_of_image RestrictedProduct.continuous_coe.continuousOn hinj
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  exact inferInstanceAs (TotallyDisconnectedSpace (FinAd F))

theorem mem_integers_iff (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F) :
    z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans
    Valued.toNormedField.norm_le_one_iff.symm

/-- Every compact subset of `𝔸_F^f` lies in a compact open subgroup. -/
theorem exists_compactOpen (C : Set (GA F)) (hC : IsCompact C) :
    ∃ H : Subgroup (GA F), IsOpen (H : Set (GA F)) ∧ IsCompact (H : Set (GA F)) ∧ C ⊆ H := by
  classical
  let pf : GA F → FinAd F := fun x => Multiplicative.toAdd x
  have hpf : Continuous pf := continuous_toAdd
  have hH : IsCompact (pf '' C) := hC.image hpf
  have hA : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
        IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Filter.Eventually.of_forall fun v =>
      ⟨isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))),
        Valued.isOpen_valuationSubring _⟩
  obtain ⟨B, hBc, hBcof, hBmem⟩ :=
    (RiemannMasullo.isCompact_closure_restrictedProduct_iff hA (pf '' C)).mp
      (by rw [hH.isClosed.closure_eq]; exact hH)
  have hbd : ∀ v, ∃ c : ℝ, ∀ z ∈ B v, ‖z‖ ≤ c := fun v => (hBc v).isBounded.exists_norm_le
  choose c hc using hbd
  let Rv : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if B v = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) then 1 else max (c v) 1
  have hRv1 : ∀ v, 1 ≤ Rv v := fun v => by
    simp only [Rv]; split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  have hHR : ∀ z ∈ pf '' C, ∀ v, ‖z v‖ ≤ Rv v := by
    intro z hz v
    by_cases hv : B v = (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · have h1 := hBmem z hz v
      rw [hv] at h1
      simp only [Rv, hv, if_true]
      exact (mem_integers_iff F v _).1 h1
    · simp only [Rv, hv, if_false]
      exact (hc v _ (hBmem z hz v)).trans (le_max_left _ _)
  let Γ' : Subgroup (GA F) :=
    { carrier := {x | ∀ v, ‖pf x v‖ ≤ Rv v}
      mul_mem' := fun {a b} ha hb v => by
        have : pf (a * b) v = pf a v + pf b v := rfl
        show ‖pf (a * b) v‖ ≤ Rv v
        rw [this]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha v) (hb v))
      one_mem' := fun v => by
        have : pf 1 v = 0 := rfl
        show ‖pf 1 v‖ ≤ Rv v
        rw [this, norm_zero]; exact zero_le_one.trans (hRv1 v)
      inv_mem' := fun {a} ha v => by
        have : pf a⁻¹ v = - pf a v := rfl
        show ‖pf a⁻¹ v‖ ≤ Rv v
        rw [this, norm_neg]; exact ha v }
  have hCΓ' : C ⊆ Γ' := fun x hx v => hHR (pf x) ⟨x, hx, rfl⟩ v
  let W : Set (FinAd F) := {z | ∀ v, ‖z v‖ ≤ Rv v}
  have hWcl : IsClosed W := by
    have : W = ⋂ v, {z : FinAd F | ‖z v‖ ≤ Rv v} := by
      ext z; simp [W]
    rw [this]
    exact isClosed_iInter fun v =>
      isClosed_le ((RestrictedProduct.continuous_eval v).norm) continuous_const
  have hWc : IsCompact W := by
    have := (RiemannMasullo.isCompact_closure_restrictedProduct_iff hA W).mpr
      ⟨fun v => Metric.closedBall 0 (Rv v), fun v => isCompact_closedBall 0 _, ?_,
        fun z hz v => mem_closedBall_zero_iff.mpr (hz v)⟩
    · rwa [hWcl.closure_eq] at this
    · filter_upwards [hBcof] with v hv
      have : Rv v = 1 := by simp [Rv, hv]
      rw [this]; ext z; rw [mem_closedBall_zero_iff]; exact (mem_integers_iff F v z).symm
  have hΓ'c : IsCompact (Γ' : Set (GA F)) := by
    have : (Γ' : Set (GA F)) = (fun z : FinAd F => (Multiplicative.ofAdd z : GA F)) '' W := by
      ext x
      constructor
      · intro hx; exact ⟨pf x, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact hz
    rw [this]
    exact hWc.image continuous_ofAdd
  have hΓ'o : IsOpen (Γ' : Set (GA F)) := by
    have hOo : IsOpen {x : GA F | ∀ v, (pf x).1 v ∈ v.adicCompletionIntegers F} :=
      (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hpf
    refine Subgroup.isOpen_of_mem_nhds Γ' (g := 1) (Filter.mem_of_superset (hOo.mem_nhds ?_) ?_)
    · intro v; exact zero_mem _
    · intro x hx v; exact ((mem_integers_iff F v _).1 (hx v)).trans (hRv1 v)
  exact ⟨Γ', hΓ'o, hΓ'c, hCΓ'⟩


theorem lc_GA : LocallyCompactSpace (GA F) := by
  obtain ⟨H, hHo, hHc, h1⟩ := exists_compactOpen F {1} isCompact_singleton
  exact hHc.locallyCompactSpace_of_mem_nhds_of_group (hHo.mem_nhds (h1 rfl))

end Adele

section Adele2
open scoped Classical
open scoped SchwartzMap

variable (F : Type*) [Field F] [NumberField F]

/-- `InfiniteAdeleRing.ringEquiv_mixedSpace` as a homeomorphism. -/
noncomputable def rhoH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun (v : InfinitePlace F) => InfinitePlace.IsReal v)
      (fun (v : InfinitePlace F) => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight
        (fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.1 v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex)))))

theorem rhoH_apply (x : InfiniteAdeleRing F) :
    rhoH F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

theorem rho_symm_eq (v : mixedEmbedding.mixedSpace F) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v = (rhoH F).symm v := by
  apply (rhoH F).injective
  rw [rhoH_apply, Homeomorph.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem continuous_rho : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F)) = ⇑(rhoH F) :=
    funext fun x => (rhoH_apply F x).symm
  rw [this]; exact (rhoH F).continuous

theorem continuous_rho_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  have : (⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) = ⇑(rhoH F).symm :=
    funext fun x => rho_symm_eq F x
  rw [this]; exact (rhoH F).symm.continuous

instance connX : ConnectedSpace (InfiniteAdeleRing F) :=
  (rhoH F).symm.surjective.connectedSpace (rhoH F).symm.continuous

theorem hX_tf : ∀ x : InfiniteAdeleRing F, (2 : ℕ) • x = 0 → x = 0 := by
  intro x hx
  have h : (2 : ℕ) • InfiniteAdeleRing.ringEquiv_mixedSpace F x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  rw [← Nat.cast_smul_eq_nsmul ℝ] at h
  have h0 := (smul_eq_zero.1 h).resolve_left (by norm_num)
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [h0, map_zero])

theorem hX_b : ∀ S : Set (InfiniteAdeleRing F), IsCompact S → ∀ x : InfiniteAdeleRing F,
    (∀ N : ℕ, N • x ∈ S) → x = 0 := by
  intro S hS x hx
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨C, hC⟩ := (hS.image (continuous_rho F)).isBounded.exists_norm_le
  have hb : ∀ N : ℕ, (N : ℝ) * ‖ρ x‖ ≤ C := fun N => by
    have := hC _ ⟨_, hx N, rfl⟩
    rwa [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at this
  have h0 : ρ x = 0 := by
    by_contra hne
    have hpos := norm_pos_iff.2 hne
    obtain ⟨N, hN⟩ := exists_nat_gt (C / ‖ρ x‖)
    have := hb N; rw [div_lt_iff₀ hpos] at hN; linarith
  exact ρ.injective (by rw [h0, map_zero])

instance lcH : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := lc_GA F
instance t2H : T2Space (FiniteAdeleRing (𝓞 F) F) := t2_GA F

instance t2G : T2Space (Multiplicative (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
instance lcG : LocallyCompactSpace (Multiplicative (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
instance scG : SecondCountableTopology (Multiplicative (AdeleRing (𝓞 F) F)) :=
  have := NumberField.AdeleRing.secondCountableTopology F
  inferInstanceAs (SecondCountableTopology (AdeleRing (𝓞 F) F))

/-- An additive subgroup of `𝔸_F^f` from a subgroup of `Multiplicative 𝔸_F^f`. -/
def toAddSub (V : Subgroup (GA F)) : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {h | Multiplicative.ofAdd h ∈ V}
  add_mem' := fun ha hb => V.mul_mem ha hb
  zero_mem' := V.one_mem
  neg_mem' := fun ha => V.inv_mem ha

theorem hH_cpt : ∀ C : Set (FiniteAdeleRing (𝓞 F) F), IsCompact C →
    ∃ V : AddSubgroup (FiniteAdeleRing (𝓞 F) F), IsOpen (V : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (V : Set (FiniteAdeleRing (𝓞 F) F)) ∧ C ⊆ V := by
  intro C hC
  obtain ⟨V, hVo, hVc, hCV⟩ :=
    exists_compactOpen F (Multiplicative.ofAdd '' C) (hC.image continuous_ofAdd)
  exact ⟨toAddSub F V, hVo, hVc, fun c hc => hCV ⟨c, hc, rfl⟩⟩

theorem hH_basis : ∀ W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F),
    ∃ V : AddSubgroup (FiniteAdeleRing (𝓞 F) F), IsOpen (V : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      (V : Set (FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  intro W hW
  have := td_GA F
  obtain ⟨C0, hC0o, hC0c, -⟩ := exists_compactOpen F {1} isCompact_singleton
  have : CompactSpace C0 := isCompact_iff_compactSpace.mp hC0c
  obtain ⟨W', hW'W, hW'o, hW'0⟩ := mem_nhds_iff.1 hW
  obtain ⟨V', hV'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((hW'o.preimage continuous_toAdd).preimage continuous_subtype_val :
      IsOpen ((Subtype.val : C0 → GA F) ⁻¹' (Multiplicative.toAdd ⁻¹' W')))
    (show Multiplicative.toAdd ((1 : C0) : GA F) ∈ W' from hW'0)
  let V : Subgroup (GA F) := V'.toOpenSubgroup.toSubgroup.map C0.subtype
  have hVo : IsOpen (V : Set (GA F)) := by
    rw [Subgroup.coe_map]; exact hC0o.isOpenMap_subtype_val _ V'.toOpenSubgroup.isOpen
  refine ⟨toAddSub F V, hVo, ?_⟩
  rintro h ⟨x, hx, hxh⟩
  have := hV' hx
  simp only [Set.mem_preimage] at this
  rw [show ((x : C0) : GA F) = Multiplicative.ofAdd h from hxh] at this
  exact hW'W this

theorem exists_equiv {m : ℕ} (L : InfiniteAdeleRing F →+ (Fin m → ℝ)) (hLc : Continuous L)
    (hLb : Function.Bijective L) :
    ∃ e' : mixedEmbedding.mixedSpace F ≃L[ℝ] (Fin m → ℝ) × (Fin 0 → ℝ),
      ∀ x, e' (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = (L x, 0) := by
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let Mh : mixedEmbedding.mixedSpace F →+ (Fin m → ℝ) :=
    L.comp ρ.symm.toAddEquiv.toAddMonoidHom
  have hMc : Continuous Mh := hLc.comp (continuous_rho_symm F)
  let Ml := Mh.toRealLinearMap hMc
  have hMl : ∀ v, Ml v = L (ρ.symm v) := fun v => rfl
  have hMb : Function.Bijective Ml := by
    have : (⇑Ml) = ⇑L ∘ ⇑ρ.symm := funext hMl
    rw [this]; exact hLb.comp ρ.symm.bijective
  let Me : mixedEmbedding.mixedSpace F ≃L[ℝ] (Fin m → ℝ) :=
    (LinearEquiv.ofBijective Ml.toLinearMap hMb).toContinuousLinearEquiv
  refine ⟨Me.trans (ContinuousLinearEquiv.prodUnique ℝ (Fin m → ℝ) (Fin 0 → ℝ)).symm,
    fun x => ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodUnique_symm_apply]
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  show Ml (ρ x) = L x
  rw [hMl, RingEquiv.symm_apply_apply]

/-- `Multiplicative (𝔸_{F,∞} × 𝔸_F^f)`. -/
abbrev GP : Type _ := Multiplicative (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem gen_mem {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g : ElemSchwartz m n r s d) :
    (fun x : AdeleRing (𝓞 F) F => extendPullback Γ π g.toFun (Multiplicative.ofAdd x)) ∈
      AdelicFourier.schwartzBruhat F := by
  have hk : IsCompact (k : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    isCompact_of_isGoodSubgroup _ k hs.2.2.1
  let Γ' : Subgroup (GP F) := Γ
  have hΓo : IsOpen (Γ' : Set (GP F)) := hs.1
  have hΓc : IsCompact (Gf (X := InfiniteAdeleRing F) Γ' : Set (FiniteAdeleRing (𝓞 F) F)) :=
    isCompact_Gf hΓo hs.2.1 (fun C hC =>
      let ⟨V, _, hVc, hCV⟩ := hH_cpt F C hC; ⟨V, hVc, hCV⟩)
  have hg := isRapidDecay_elemSchwartz_toFun g
  obtain ⟨rfl, rfl, L, b, Wf, hLc, hLb, hWo, hWΓ, hform, hbinv⟩ :=
    core (X := InfiniteAdeleRing F) (H := FiniteAdeleRing (𝓞 F) F) (Γ := Γ') π (hX_tf F)
      (hX_b F) (hH_basis F) hk hΓo hΓc hπ
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨e', he'⟩ := exists_equiv F L hLc hLb
  have : ∀ i, NeZero (d i) := fun i => ⟨hπ.1 i⟩
  let Gb : ((i : Fin s) → ZMod (d i)) → 𝓢(mixedEmbedding.mixedSpace F, ℂ) := fun b' =>
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e' (schwartzOfRapid hg b')
  let hb : ((i : Fin s) → ZMod (d i)) → FiniteAdeleRing (𝓞 F) F → ℂ := fun b' y =>
    if y ∈ Gf (X := InfiniteAdeleRing F) Γ' ∧ b y = b' then 1 else 0
  have hsum : (fun x : AdeleRing (𝓞 F) F => extendPullback Γ π g.toFun (Multiplicative.ofAdd x)) =
      ∑ b' : ((i : Fin s) → ZMod (d i)),
        (fun x : AdeleRing (𝓞 F) F => Gb b' (ρ x.1) * hb b' x.2) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : Multiplicative.ofAdd x ∈ Γ
    · have hx2 : x.2 ∈ Gf (X := InfiniteAdeleRing F) Γ' :=
        (mem_iff_snd_mem_Gf hΓo (Multiplicative.ofAdd x)).1 hx
      simp only [extendPullback, dif_pos hx, hb, hx2, true_and, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      obtain ⟨h1, h2⟩ := hform _ hx
      show g.toFun _ = schwartzOfRapid hg (b x.2) (e' (ρ x.1))
      rw [schwartzOfRapid_apply, he']
      show g.toFun _ = g.toFun _
      congr 1
      exact Prod.ext h1 (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) h2))
    · have hx2 : x.2 ∉ Gf (X := InfiniteAdeleRing F) Γ' :=
        fun h => hx ((mem_iff_snd_mem_Gf hΓo _).2 h)
      simp only [extendPullback, dif_neg hx, hb, hx2, false_and, if_false, mul_zero,
        Finset.sum_const_zero]
  rw [hsum]
  refine Submodule.sum_mem _ fun b' _ => Submodule.subset_span ⟨Gb b', hb b', ?_, ?_, rfl⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun y =>
      ⟨(fun z => z - y) ⁻¹' Wf, hWo.preimage (continuous_id.sub continuous_const),
        by simp [Wf.zero_mem], fun z hz => ?_⟩
    have hz' : z = y + (z - y) := by abel
    rw [hz']
    have hmem : y + (z - y) ∈ Gf (X := InfiniteAdeleRing F) Γ' ↔
        y ∈ Gf (X := InfiniteAdeleRing F) Γ' :=
      ⟨fun h => by simpa using (Gf Γ').sub_mem h (hWΓ hz), fun h => (Gf Γ').add_mem h (hWΓ hz)⟩
    simp only [hb]
    rw [hbinv y _ hz, hmem]
  · exact HasCompactSupport.intro hΓc fun y hy => by
      simp only [hb]; rw [if_neg]; exact fun h => hy h.1

theorem pure_mem {g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)} {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ f : AdelicSchwartz F,
      f.eval = fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2 := by
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace F
  -- a compact open subgroup containing the support of `h`
  obtain ⟨Γf, hΓfo, hΓfc, hsupp⟩ := hH_cpt F _ hcs
  -- a neighbourhood `W` of `0` under whose translations `h` is invariant
  have hO : IsOpen {p : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F |
      h (p.1 + p.2) = h p.1} := by
    have := ((hlc.comp_continuous continuous_add).comp₂ (hlc.comp_continuous continuous_fst)
      (· = ·)) {True}
    convert this using 1
    ext p; simp
  obtain ⟨u, v, -, hvo, hΓu, h0v, huv⟩ := generalized_tube_lemma hΓfc
    (isCompact_singleton (x := (0 : FiniteAdeleRing (𝓞 F) F))) hO
    (by
      rintro ⟨p1, p2⟩ ⟨-, hp2⟩
      have hp2' : p2 = 0 := hp2
      show h (p1 + p2) = h p1
      rw [hp2', add_zero])
  let W : Set (FiniteAdeleRing (𝓞 F) F) := v ∩ Γf
  have hWo : IsOpen W := hvo.inter hΓfo
  have hW0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ W := ⟨h0v rfl, Γf.zero_mem⟩
  have hnot : ∀ y, y ∉ (Γf : Set (FiniteAdeleRing (𝓞 F) F)) → h y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun h' => hy (hsupp h'))
  have hWinv : ∀ y, ∀ w ∈ W, h (y + w) = h y := by
    intro y w hw
    by_cases hy : y ∈ Γf
    · exact huv (Set.mk_mem_prod (hΓu hy) hw.1)
    · have : y + w ∉ Γf := fun h' => hy (by simpa using Γf.sub_mem h' hw.2)
      rw [hnot _ this, hnot _ hy]
  -- a small good subgroup
  obtain ⟨kN, -, hsmall, hgood, hpres⟩ :=
    exists_small_good_subgroups (Multiplicative (AdeleRing (𝓞 F) F))
  let U : Set (Multiplicative (AdeleRing (𝓞 F) F)) := {y | (Multiplicative.toAdd y).2 ∈ W}
  have hU : U ∈ 𝓝 (1 : Multiplicative (AdeleRing (𝓞 F) F)) :=
    (hWo.preimage (continuous_snd.comp continuous_toAdd)).mem_nhds hW0
  obtain ⟨N, hN⟩ := hsmall U hU
  -- the open subgroup `𝔸_{F,∞} × Γf`
  let Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)) :=
    { carrier := {y | (Multiplicative.toAdd y).2 ∈ Γf}
      mul_mem' := fun ha hb => Γf.add_mem ha hb
      one_mem' := Γf.zero_mem
      inv_mem' := fun ha => Γf.neg_mem ha }
  have hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    hΓfo.preimage (continuous_snd.comp continuous_toAdd)
  have hkΓ : kN N ≤ Γ := fun y hy => (hN hy).2
  have hcg : IsCompactlyGeneratedSubgroup Γ := by
    let θ : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F →
        Multiplicative (AdeleRing (𝓞 F) F) :=
      fun p => Multiplicative.ofAdd (((rhoH F).symm p.1, p.2) : AdeleRing (𝓞 F) F)
    have hθ : Continuous θ :=
      continuous_ofAdd.comp (((rhoH F).symm.continuous.comp continuous_fst).prodMk continuous_snd)
    have hθ0 : ∀ y : FiniteAdeleRing (𝓞 F) F, θ (0, y) =
        Multiplicative.ofAdd (((0 : InfiniteAdeleRing F), y) : AdeleRing (𝓞 F) F) := by
      intro y
      show Multiplicative.ofAdd (((rhoH F).symm 0, y) : AdeleRing (𝓞 F) F) = _
      rw [← rho_symm_eq, map_zero]
    let U0 := θ '' (Metric.closedBall 0 1 ×ˢ (Γf : Set (FiniteAdeleRing (𝓞 F) F)))
    refine ⟨U0, ((isCompact_closedBall _ _).prod hΓfc).image hθ, ?_,
      ⟨{y | ρ (Multiplicative.toAdd y).1 ∈ Metric.ball 0 1}, ?_, ?_⟩, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩; exact hp.2
    · refine (Metric.isOpen_ball.preimage
        ((continuous_rho F).comp (continuous_fst.comp continuous_toAdd))).mem_nhds ?_
      show ρ (0 : InfiniteAdeleRing F) ∈ Metric.ball 0 1
      rw [map_zero]; exact Metric.mem_ball_self one_pos
    · rintro y ⟨hy1, hy2⟩
      refine ⟨(ρ (Multiplicative.toAdd y).1, (Multiplicative.toAdd y).2),
        ⟨Metric.ball_subset_closedBall hy1, hy2⟩, ?_⟩
      show Multiplicative.ofAdd (((rhoH F).symm (ρ _), _) : AdeleRing (𝓞 F) F) = y
      rw [← rho_symm_eq, RingEquiv.symm_apply_apply]; rfl
    · apply le_antisymm
      · rw [Subgroup.closure_le]; rintro _ ⟨p, hp, rfl⟩; exact hp.2
      · intro y hy
        have hdec : y = Multiplicative.ofAdd (((Multiplicative.toAdd y).1, 0) : AdeleRing (𝓞 F) F) *
            Multiplicative.ofAdd (((0 : InfiniteAdeleRing F), (Multiplicative.toAdd y).2) :
              AdeleRing (𝓞 F) F) := by
          apply Multiplicative.toAdd.injective
          show (Multiplicative.toAdd y : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) =
            ((Multiplicative.toAdd y).1, 0) + (0, (Multiplicative.toAdd y).2)
          rw [Prod.mk_add_mk, add_zero, zero_add]
          rfl
        rw [hdec]
        refine Subgroup.mul_mem _ ?_ (Subgroup.subset_closure
          ⟨(0, (Multiplicative.toAdd y).2), ⟨by simp, hy⟩, hθ0 _⟩)
        obtain ⟨K, hK⟩ := exists_nat_gt ‖ρ (Multiplicative.toAdd y).1‖
        have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (norm_nonneg _) hK
        set z := ρ.symm (((K : ℝ)⁻¹) • ρ (Multiplicative.toAdd y).1) with hz_def
        have hzU : Multiplicative.ofAdd ((z, 0) : AdeleRing (𝓞 F) F) ∈ U0 := by
          refine ⟨(((K : ℝ)⁻¹) • ρ (Multiplicative.toAdd y).1, 0), ⟨?_, Γf.zero_mem⟩, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_natCast]
            rw [inv_mul_le_iff₀ hKpos, mul_one]; exact hK.le
          · show Multiplicative.ofAdd (((rhoH F).symm _, 0) : AdeleRing (𝓞 F) F) = _
            rw [← rho_symm_eq]
        have hpow : Multiplicative.ofAdd (((Multiplicative.toAdd y).1, 0) : AdeleRing (𝓞 F) F) =
            (Multiplicative.ofAdd ((z, 0) : AdeleRing (𝓞 F) F)) ^ K := by
          apply Multiplicative.toAdd.injective
          show (((Multiplicative.toAdd y).1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) =
            K • ((z, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
          rw [Prod.smul_mk, smul_zero]
          refine Prod.ext ?_ rfl
          show (Multiplicative.toAdd y).1 = K • z
          apply ρ.injective
          rw [map_nsmul, hz_def, RingEquiv.apply_symm_apply, ← Nat.cast_smul_eq_nsmul ℝ,
            smul_smul, mul_inv_cancel₀ hKpos.ne', one_smul]
        rw [hpow]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure hzU) K
  have hs : IsStructuralPair Γ (kN N) := ⟨hΓo, hcg, hgood N, hkΓ⟩
  obtain ⟨m, n, r, s, d, π, hπ⟩ := hpres N Γ hΓo hcg hkΓ
  have hk : IsCompact (kN N : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    isCompact_of_isGoodSubgroup _ _ (hgood N)
  let Γ' : Subgroup (GP F) := Γ
  have hΓo' : IsOpen (Γ' : Set (GP F)) := hΓo
  have hΓc : IsCompact (Gf (X := InfiniteAdeleRing F) Γ' : Set (FiniteAdeleRing (𝓞 F) F)) :=
    hΓfc
  obtain ⟨rfl, rfl, L, b, Wf, hLc, hLb, -, -, hform, -⟩ :=
    core (X := InfiniteAdeleRing F) (H := FiniteAdeleRing (𝓞 F) F) (Γ := Γ') π (hX_tf F)
      (hX_b F) (hH_basis F) hk hΓo' hΓc hπ
  obtain ⟨e', he'⟩ := exists_equiv F L hLc hLb
  obtain ⟨M, hM⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  let sec := Function.surjInv hπ.2.2.2.1
  let c : ((i : Fin s) → ZMod (d i)) → ℂ := fun b' =>
    h (Multiplicative.toAdd ((sec (Multiplicative.ofAdd ((0, 0, 0, b') : ElemGroup m 0 0 s d)) :
      Multiplicative (AdeleRing (𝓞 F) F)))).2
  let Φ : 𝓢((Fin m → ℝ) × (Fin 0 → ℝ), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e'.symm g
  let Gfun : ElemGroup m 0 0 s d → ℂ := fun e => Φ (e.1, 0) * c e.2.2.2
  have hrd : IsRapidDecay Gfun := isRapidDecay_of_schwartz Φ c M (fun b' => hM _)
  let gs : ElemSchwartz m 0 0 s d := ⟨Gfun, Submodule.subset_span hrd⟩
  refine ⟨SchwartzBruhat.ofElem Γ (kN N) π hs hπ gs, ?_⟩
  funext x
  show extendPullback Γ π Gfun (Multiplicative.ofAdd x) = _
  by_cases hx : Multiplicative.ofAdd x ∈ Γ
  · rw [extendPullback, dif_pos hx]
    obtain ⟨h1, h2⟩ := hform _ hx
    show Φ ((Multiplicative.toAdd (π ⟨_, hx⟩)).1, 0) * c (Multiplicative.toAdd (π ⟨_, hx⟩)).2.2.2 = _
    have h1' : (Multiplicative.toAdd (π ⟨Multiplicative.ofAdd x, hx⟩)).1 = L x.1 := h1
    have h2' : (Multiplicative.toAdd (π ⟨Multiplicative.ofAdd x, hx⟩)).2.2.2 = b x.2 := h2
    rw [h1', h2']
    have hΦ : Φ (L x.1, 0) = g (ρ x.1) := by
      show g (e'.symm _) = _
      congr 1
      rw [ContinuousLinearEquiv.symm_apply_eq, he']
    rw [hΦ]
    congr 1
    set x₀ := sec (Multiplicative.ofAdd ((0, 0, 0, b x.2) : ElemGroup m 0 0 s d))
    have hx₀ : π x₀ = Multiplicative.ofAdd ((0, 0, 0, b x.2) : ElemGroup m 0 0 s d) :=
      Function.surjInv_eq hπ.2.2.2.1 _
    have hiH : (iH (X := InfiniteAdeleRing F) x.2 : GP F) ∈ Γ' := hx
    have hπiH : π ⟨iH x.2, hiH⟩ = π x₀ := by
      rw [hx₀]
      obtain ⟨k1, k2⟩ := hform _ hiH
      apply Multiplicative.toAdd.injective
      refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
      · exact k1.trans L.map_zero
      · exact k2
    have hmemk : ((x₀⁻¹ * ⟨iH x.2, hiH⟩ : Γ) : Multiplicative (AdeleRing (𝓞 F) F)) ∈ kN N := by
      rw [← hπ.2.2.2.2, map_mul, map_inv, hπiH, inv_mul_cancel]
    have hw := (hN hmemk : (Multiplicative.toAdd
      ((x₀⁻¹ * ⟨iH x.2, hiH⟩ : Γ) : Multiplicative (AdeleRing (𝓞 F) F))).2 ∈ W)
    have key := hWinv (Multiplicative.toAdd (x₀ : Multiplicative (AdeleRing (𝓞 F) F))).2 _ hw
    have e2 : (Multiplicative.toAdd (x₀ : Multiplicative (AdeleRing (𝓞 F) F))).2 +
        (Multiplicative.toAdd ((x₀⁻¹ * ⟨iH x.2, hiH⟩ : Γ) :
          Multiplicative (AdeleRing (𝓞 F) F))).2 = x.2 := by
      show _ + (-(Multiplicative.toAdd (x₀ : Multiplicative (AdeleRing (𝓞 F) F))).2 + x.2) = x.2
      abel
    rw [e2] at key
    exact key.symm
  · rw [extendPullback, dif_neg hx]
    have : x.2 ∉ (Γf : Set (FiniteAdeleRing (𝓞 F) F)) := hx
    rw [hnot _ this, mul_zero]

end Adele2

end Sol_MasulloGRH_adelicSchwartz_range_eval_eq_schwartzBruhat

open Sol_MasulloGRH_adelicSchwartz_range_eval_eq_schwartzBruhat in
open MasulloGRH in
theorem solution
    (F : Type*) [Field F] [NumberField F] :
    Set.range (fun f : AdelicSchwartz F => f.eval) =
      (NumberField.AdelicFourier.schwartzBruhat F : Set (AdeleRing (𝓞 F) F → ℂ)) := by
  ext φ
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    show (fun x : AdeleRing (𝓞 F) F => f (Multiplicative.ofAdd x)) ∈
      NumberField.AdelicFourier.schwartzBruhat F
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
      exact gen_mem F π hs hπ g
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · intro hφ
    have hφ' : φ ∈ Submodule.span ℂ (NumberField.AdelicFourier.pureTensorSet F) := hφ
    clear hφ
    induction hφ' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, h, hlc, hcs, rfl⟩ := hx
      obtain ⟨f, hf⟩ := pure_mem F hlc hcs
      exact ⟨f, hf⟩
    | zero => exact ⟨0, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨f', rfl⟩ := hy
      exact ⟨f + f', rfl⟩
    | smul a x _ hx =>
      obtain ⟨f, rfl⟩ := hx
      exact ⟨a • f, rfl⟩
