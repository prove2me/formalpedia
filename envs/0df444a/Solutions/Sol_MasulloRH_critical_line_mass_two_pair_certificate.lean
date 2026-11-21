-- Prove2me | solution 1 for MasulloRH.critical_line_mass_two_pair_certificate
-- status  : ACCEPTED   (prove)
-- author  : @meadowlark
-- created : 2026-11-21T01:41:04.535013+00:00
-- url     : https://prove2.me/submissions/ff96c64f-7a65-4c6e-917d-fd6e3cf9e74b

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_critical_line_mass_first_pair_certificate


/-
The interval proof adapts Thomas Lince's teal-sea/zeta-lab, commit
a401821c9608526425f3d4cf7ff8e59bc37e1c79 (hunts/hardy_first_zero and
lean/ZetaLean), through Ricardo Marangoni Brandao Bueno's Lean 4.33.1
Prove2Me port, accepted submission 0f7a110c-a652-4faf-870f-71bf9c5f9f22.
This adaptation changes the interval, regenerates the rational rectangles
and Euler–Maclaurin remainders, and instantiates the gamma phase anew.
Thomas Lince's hunt #133, HardyTenZeros.zero_in_2102, had already proved
the existence of a zero in the overlapping interval (21.02, 21.03) on
Lean v4.35.0-rc2. No priority is claimed for the zero localization.

The Real.arctan_le_self backport follows Mathlib at commit
065356127b1dc0016f66b7283ce0ce2c4055aa55, file
Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean.
Copyright (c) 2022 David Loeffler. All rights reserved.
Authors: David Loeffler, Yaël Dillies, Bhavik Mehta. Apache-2.0.

MIT License

Copyright (c) 2026 Thomas Lince

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/


section
-- Backport of the arctangent bound from Mathlib Trigonometric.Bounds.
theorem Real.arctan_le_self {x : ℝ} (h : 0 ≤ x) : Real.arctan x ≤ x := by
  simpa using Real.le_tan (Real.arctan_nonneg.mpr h) (Real.arctan_lt_pi_div_two x)
set_option maxHeartbeats 2500000
set_option maxRecDepth 100000


/- SOURCE: lean/ZetaLean/HardyZ.lean -/






open Complex
open scoped ComplexConjugate

/--
Hardy's Z function.

Defined using the completed Riemann zeta function `Λ(s)` to avoid
needing a continuous branch of `log Γ` along the critical line.
Since `Λ(1/2 + it)` is real, we divide by the positive real factor
`π^(-1/4) * ‖Γ(1/4 + I*t/2)‖` to obtain `Z(t)`.

Note: The goal is to eventually type this as `ℝ → ℝ` if preferred by Mathlib,
but here we start with the definition over `ℂ` or returning `ℂ` for easier
algebra before extracting the real part or proving it's real.
-/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  completedRiemannZeta (1/2 + t * I) /
    ( (Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * ‖Gamma (1/4 + t / 2 * I)‖ )

lemma Gammaℝ_conj (s : ℂ) : conj (Gammaℝ s) = Gammaℝ (conj s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Gamma_conj]
  have hpi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  have h1 := (cpow_conj (↑Real.pi) (-s/2) hpi).symm
  rw [conj_ofReal] at h1
  rw [h1]
  congr 1
  · congr 1
    rw [map_div₀, map_neg]
    congr 2
    exact map_ofNat (starRingEnd ℂ) 2
  · congr 1
    rw [map_div₀]
    congr 1
    exact map_ofNat (starRingEnd ℂ) 2

lemma completedRiemannZeta_conj_half (t : ℝ) :
    conj (completedRiemannZeta (1/2 + t * I)) = completedRiemannZeta (1/2 - t * I) := by
  let s : ℂ := 1/2 + t * I
  have hs_re : 0 < s.re := by
    dsimp [s]; simp
  have hcs_re : 0 < (conj s).re := by
    rw [conj_re]; exact hs_re
  have H1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h_s_ne_zero : s ≠ 0 := by
      intro h
      have : s.re = 0 := by rw [h, zero_re]
      linarith
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs_re)).symm
  have H2 : completedRiemannZeta (conj s) = riemannZeta (conj s) * Gammaℝ (conj s) := by
    have h_s_ne_zero : conj s ≠ 0 := by
      intro h
      have : (conj s).re = 0 := by rw [h, zero_re]
      linarith
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hcs_re)).symm
  have h_conj_s : conj (1/2 + (t:ℂ) * I) = 1/2 - t * I := by
    apply Complex.ext <;> simp
  rw [← h_conj_s]
  change conj (completedRiemannZeta s) = completedRiemannZeta (conj s)
  rw [H1, H2, map_mul, ← riemannZeta_conj, Gammaℝ_conj]

/-- `Z t` is strictly real. -/
lemma hardyZ_is_real (t : ℝ) : ∃ (r : ℝ), hardyZ t = r := by
  use (hardyZ t).re
  symm
  apply conj_eq_iff_re.mp
  dsimp [hardyZ]
  rw [map_div₀, completedRiemannZeta_conj_half]
  congr 1
  · have h_symm : 1/2 - (t:ℂ) * I = 1 - (1/2 + (t:ℂ) * I) := by ring
    rw [h_symm, completedRiemannZeta_one_sub]
  · rw [map_mul]
    congr 1
    · have hpi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
        rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
      have h1 := (cpow_conj (↑Real.pi) (-(1/4:ℝ)) hpi).symm
      rw [conj_ofReal, map_neg, conj_ofReal] at h1
      exact h1
    · exact conj_ofReal _

/-- The absolute value of `Z t` is exactly the absolute value of `ζ(1/2 + it)`. -/
lemma abs_hardyZ_eq_abs_zeta (t : ℝ) : ‖hardyZ t‖ = ‖riemannZeta (1/2 + t * I)‖ := by
  dsimp [hardyZ]
  rw [norm_div]
  let s : ℂ := 1/2 + t * I
  have hs_re : 0 < s.re := by
    dsimp [s]
    norm_num
  have h_s_ne_zero : s ≠ 0 := by
    intro h
    have h_re : s.re = 0 := by rw [h, zero_re]
    dsimp [s] at h_re
    norm_num at h_re
  have H1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs_re)).symm
  rw [H1, norm_mul]
  have H3 : ‖(↑Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * (‖Gamma (1/4 + ↑t / 2 * I)‖ : ℂ)‖ = ‖Gammaℝ s‖ := by
    rw [Gammaℝ_def, norm_mul, norm_mul]
    congr 1
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      have H_re : (-(1/4 : ℝ) : ℂ).re = (-s/2).re := by
        dsimp [s]; simp; norm_num
      exact H_re
    · rw [Complex.norm_of_nonneg (norm_nonneg _)]
      congr 1
      have H_eq : 1/4 + (t:ℂ) / 2 * I = s / 2 := by
        dsimp [s]; apply Complex.ext <;> simp <;> ring
      rw [H_eq]
  rw [H3, mul_div_cancel_right₀]
  rw [norm_ne_zero_iff]
  exact Gammaℝ_ne_zero_of_re_pos hs_re


/-- `Z t` is zero if and only if `ζ(1/2 + it)` is zero. -/
lemma hardyZ_zero_iff (t : ℝ) : hardyZ t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  have h1 : hardyZ t = 0 ↔ ‖hardyZ t‖ = 0 := norm_eq_zero.symm
  have h2 : riemannZeta (1/2 + (t:ℂ) * I) = 0 ↔ ‖riemannZeta (1/2 + (t:ℂ) * I)‖ = 0 := norm_eq_zero.symm
  rw [h1, h2, abs_hardyZ_eq_abs_zeta]

/-- `Z t` is continuous. -/
lemma continuous_hardyZ : Continuous hardyZ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  unfold hardyZ
  apply ContinuousAt.div
  · let f (t : ℝ) : ℂ := 1/2 + (t : ℂ) * I
    have h1 : ContinuousAt f x := by
      have h_cont : Continuous f := by
        refine continuous_const.add ?_
        refine Continuous.mul continuous_ofReal continuous_const
      exact h_cont.continuousAt
    have hs0 : f x ≠ 0 := by
      intro h; have h_re : (f x).re = 0 := by rw [h, zero_re]
      dsimp [f] at h_re; norm_num at h_re
    have hs1 : f x ≠ 1 := by
      intro h; have h_re : (f x).re = 1 := by rw [h, one_re]
      dsimp [f] at h_re; norm_num at h_re
    exact (differentiableAt_completedZeta hs0 hs1).continuousAt.comp h1
  · have H_const : ContinuousAt (fun (t : ℝ) => (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ)) x := continuousAt_const
    let f (t : ℝ) : ℂ := 1 / 4 + (t : ℂ) / 2 * I
    have H_arg : ContinuousAt f x := by
      have h_cont : Continuous f := by
        refine continuous_const.add ?_
        refine Continuous.mul ?_ continuous_const
        refine Continuous.div continuous_ofReal continuous_const ?_
        intro _; exact two_ne_zero
      exact h_cont.continuousAt
    have H_gamma : ContinuousAt (fun (t : ℝ) => (‖Gamma (f t)‖ : ℂ)) x := by
      have hc1 : ContinuousAt Gamma (f x) := by
        apply continuousAt_Gamma
        intro m h_eq
        have h_re : (f x).re = (-m : ℂ).re := by rw [h_eq]
        dsimp [f] at h_re; simp at h_re
        have hm : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
        linarith
      exact continuous_ofReal.continuousAt.comp (continuous_norm.continuousAt.comp (hc1.comp H_arg))
    exact H_const.mul H_gamma
  · intro h
    let f (t : ℝ) : ℂ := 1 / 4 + (t : ℂ) / 2 * I
    have h_mul : (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ) * (‖Gamma (f x)‖ : ℂ) = 0 := h
    rw [mul_eq_zero] at h_mul
    cases h_mul with
    | inl h_pi =>
      have H_pi_ne : (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ) ≠ 0 := by
        intro h_eq
        have h_norm : ‖(↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ)‖ = 0 := by rw [h_eq, norm_zero]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at h_norm
        have h_re : (-(1 / 4 : ℝ) : ℂ).re = -1 / 4 := by norm_num
        rw [h_re] at h_norm
        have h_pos : (Real.pi : ℝ) ^ (-1/4 : ℝ) > 0 := Real.rpow_pos_of_pos Real.pi_pos _
        linarith
      exact H_pi_ne h_pi
    | inr h_gamma =>
      have H_g_norm_zero : ‖Gamma (f x)‖ = 0 := by
        exact (Complex.ofReal_eq_zero).mp h_gamma
      rw [norm_eq_zero] at H_g_norm_zero
      have H_g_ne_zero : Gamma (f x) ≠ 0 := by
        apply Gamma_ne_zero
        intro m h_eq
        have h_re : (f x).re = (-m : ℂ).re := by rw [h_eq]
        dsimp [f] at h_re; simp at h_re
        have hm : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
        linarith
      exact H_g_ne_zero H_g_norm_zero

/-!
### The real-valued Z

`hardyZ_is_real` proves every value of `hardyZ` equals some real number, but
`hardyZ` itself is still typed `ℝ → ℂ`: the docstring at the top of this file
flagged that as provisional ("the goal is to eventually type this as
`ℝ → ℝ`"). This section meets that goal, purely additively: `hardyZReal` and
everything below are *derived* from the five lemmas above via the coercion
`ℝ → ℂ`, without editing a single one of them, so nothing already
kernel-checked is put at risk by this section existing.
-/

/-- Hardy's Z, retyped `ℝ → ℝ` now that `hardyZ_is_real` is proved. -/
noncomputable def hardyZReal (t : ℝ) : ℝ := (hardyZ t).re

/-- `hardyZReal` and `hardyZ` agree under the standard `ℝ → ℂ` coercion. -/
lemma hardyZReal_eq_hardyZ (t : ℝ) : (hardyZReal t : ℂ) = hardyZ t := by
  obtain ⟨r, hr⟩ := hardyZ_is_real t
  unfold hardyZReal
  rw [hr, Complex.ofReal_re]



/-- `hardyZReal t = 0` iff `ζ(1/2 + it) = 0`. -/
lemma hardyZReal_zero_iff (t : ℝ) :
    hardyZReal t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  rw [← hardyZ_zero_iff t, ← hardyZReal_eq_hardyZ t, Complex.ofReal_eq_zero]

/-- `hardyZReal` is continuous. -/
lemma continuous_hardyZReal : Continuous hardyZReal :=
  Complex.continuous_re.comp continuous_hardyZ


/- SOURCE: hunts/hardy_first_zero/lean/HardyFirstZero/Spine.lean -/




/-!
# The sign test behind the first zero (hunt `hardy_first_zero`)

The reduction this hunt's Lean plan rests on, kernel-checked: a zero of `ζ` on
the critical line between `a` and `b` follows from two inequalities, and neither
of them asks for the value of the Riemann-Siegel phase.

* `hX`: `Re (ζ(1/2 + ia) · conj ζ(1/2 + ib)) < 0`, a statement about two values
  of `ζ` that an Euler-Maclaurin enclosure can decide;
* `hG`: `0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib))`, which says only that the
  phase of `Γℝ` turns by less than a quarter turn between `a` and `b`.

Why that suffices: `hardyZ t = Λ(1/2 + it) / d(t)` with `d(t) > 0`
(`ZetaLean/HardyZ.lean`), and `Λ = ζ · Γℝ` off the poles, so
`Z(a) Z(b) d(a) d(b) = X G` with `X` and `G` the two products above. The left
side is real, so multiplying by `conj X` and taking real parts gives
`Z(a) Z(b) d(a) d(b) Re X = ‖X‖² Re G > 0`, hence `Z(a) Z(b) < 0`, and the
intermediate value theorem on the continuous real `hardyZReal` finishes.

Nothing here is numerical. The two hypotheses are the open work: `hX` needs an
evaluation of `ζ` with a proved error bound, `hG` a crude bound on the phase
of `Γ` (`RESULTS.md`, routes E and P).
-/

open Complex
open scoped ComplexConjugate

namespace HardyFirstZero

/-- The critical-line point `1/2 + it`. -/
noncomputable abbrev sOf (t : ℝ) : ℂ := 1 / 2 + t * I

lemma sOf_re (t : ℝ) : (sOf t).re = 1 / 2 := by simp [sOf]

lemma sOf_ne_zero (t : ℝ) : sOf t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [sOf_re, Complex.zero_re] at this
  norm_num at this

/-- `Λ(1/2 + it) = ζ(1/2 + it) · Γℝ(1/2 + it)`. -/
lemma completed_eq (t : ℝ) :
    completedRiemannZeta (sOf t) = riemannZeta (sOf t) * Gammaℝ (sOf t) := by
  have hre : 0 < (sOf t).re := by rw [sOf_re]; norm_num
  rw [riemannZeta_def_of_ne_zero (sOf_ne_zero t)]
  exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hre)).symm

/-- The positive real denominator of `hardyZ`. -/
noncomputable def den (t : ℝ) : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * ‖Gamma (1 / 4 + t / 2 * I)‖

lemma den_pos (t : ℝ) : 0 < den t := by
  unfold den
  refine mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (norm_pos_iff.mpr ?_)
  apply Gamma_ne_zero_of_re_pos
  simp

lemma hardyZ_eq (t : ℝ) : hardyZ t = completedRiemannZeta (sOf t) / ((den t : ℝ) : ℂ) := by
  unfold hardyZ den sOf
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_neg]

/-- `Z(a) Z(b) d(a) d(b) = (ζ_a conj ζ_b) (Γℝ_a conj Γℝ_b)`, as complex numbers. -/
lemma hardyZReal_mul (a b : ℝ) :
    ((hardyZReal a * hardyZReal b : ℝ) : ℂ) * ((den a * den b : ℝ) : ℂ)
      = (riemannZeta (sOf a) * conj (riemannZeta (sOf b)))
        * (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))) := by
  have hb : ((hardyZReal b : ℝ) : ℂ) = conj (hardyZ b) := by
    rw [← hardyZReal_eq_hardyZ b, Complex.conj_ofReal]
  have hda : ((den a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (den_pos a).ne'
  have hdb : ((den b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (den_pos b).ne'
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hb, hardyZReal_eq_hardyZ a, hardyZ_eq a,
    hardyZ_eq b, map_div₀, Complex.conj_ofReal, completed_eq a, completed_eq b, map_mul]
  field_simp

/-- The algebraic core: a real `P` with `P d = X G`, `d > 0`, `Re X < 0` and
`Re G > 0` is negative. -/
lemma neg_of_mul_eq {P d : ℝ} {X G : ℂ} (hd : 0 < d) (h : (P : ℂ) * (d : ℂ) = X * G)
    (hX : X.re < 0) (hG : 0 < G.re) : P < 0 := by
  have h2 : (P : ℂ) * (d : ℂ) * conj X = ((‖X‖ ^ 2 : ℝ) : ℂ) * G := by
    rw [h, Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  have h3 := congrArg Complex.re h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, mul_zero, add_zero, sub_zero] at h3
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hX
    exact lt_irrefl 0 hX
  have hn : 0 < ‖X‖ ^ 2 := by positivity
  have hrhs : 0 < ‖X‖ ^ 2 * G.re := mul_pos hn hG
  -- `P d Re X > 0` with `d > 0` and `Re X < 0` forces `P < 0`
  by_contra hP
  replace hP := not_lt.mp hP
  have : P * d * X.re ≤ 0 := by
    have hPd : 0 ≤ P * d := mul_nonneg hP hd.le
    exact mul_nonpos_of_nonneg_of_nonpos hPd hX.le
  linarith

/-- **The sign test.** Two inequalities, one about `ζ` and one about `Γℝ`,
give a zero of `ζ` on the critical line strictly between `a` and `b`. -/
theorem exists_zero_of_sign_data {a b : ℝ} (hab : a < b)
    (hX : (riemannZeta (sOf a) * conj (riemannZeta (sOf b))).re < 0)
    (hG : 0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hP : hardyZReal a * hardyZReal b < 0 :=
    neg_of_mul_eq (mul_pos (den_pos a) (den_pos b)) (hardyZReal_mul a b) hX hG
  have hc : ContinuousOn hardyZReal (Set.Icc a b) := continuous_hardyZReal.continuousOn
  rcases mul_neg_iff.mp hP with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨t, ht, (hardyZReal_zero_iff t).mp h0⟩
  · obtain ⟨t, ht, h0⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨t, ht, (hardyZReal_zero_iff t).mp h0⟩

end HardyFirstZero


/- SOURCE: hunts/hardy_first_zero/lean/HardyFirstZero/Phase.lean -/







/-!
# The phase of `Γℝ` turns slowly (hunt `hardy_first_zero`, route P)

`Spine.lean` reduces the first zero to two inequalities. This file proves the one
about `Γ`, for any `0 < a < b` whose gap is small enough, with no evaluation of
`Γ` anywhere:

    0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib)).

**The route.** Write `z = 1/4 + ia/2`, `w = 1/4 - ib/2`, `δ = (b - a)/2`,
`K = ab/4` and `c_j = j + 1/4`. Up to the positive factor `π^{-1/2}`, the
product is `V = π^{iδ} Γ(z) Γ(w)`, and Euler's limit (`Complex.GammaSeq_tendsto_Gamma`)
gives `V = lim V_n` with `V_n = π^{iδ} GammaSeq z n · GammaSeq w n`. Each `V_n` is
explicit: `(z + j)(w + j) = (c_j² + K) - i δ c_j`, so

    V_n = R_n · exp(i φ_n),   φ_n = δ log π - δ log n + Σ_{j ≤ n} arctan(δ c_j / (c_j² + K)),

with `R_n > 0`. Elementary bounds (`arctan x ≤ x`, `arctan x ≥ x - x³`, the
harmonic-number bounds of `Mathlib.NumberTheory.Harmonic.Bounds`, `Σ 1/j² ≤ 2`)
confine every `φ_n`, `n ≥ 1`, to `[-(δ(1 + 2K) + 66 δ³), δ(π + 4)]`, so
`Re V_n ≥ cos L · ‖V_n‖` with `L < π/2`, and the inequality survives the limit.

The window is crude on purpose: at `a = 14.13`, `b = 14.14` the true phase
increment is `-0.00405` while the window is `[-0.5045, 0.0357]`. Nothing here
needs the digamma function or Stirling's formula.
-/

open Complex Finset Filter
open scoped ComplexConjugate Topology

namespace HardyFirstZero

/-! ### One factor in polar form -/

/-- `A - iB = √(A² + B²) · exp(-i · arctan(B/A))` for `A > 0`. -/
lemma polar_of_re_pos {A B : ℝ} (hA : 0 < A) :
    ((A : ℂ) - (B : ℂ) * I)
      = ((Real.sqrt (A ^ 2 + B ^ 2) : ℝ) : ℂ) * exp (-(Real.arctan (B / A) : ℂ) * I) := by
  set θ := Real.arctan (B / A) with hθ
  have hsq : Real.sqrt (A ^ 2 + B ^ 2) = A * Real.sqrt (1 + (B / A) ^ 2) := by
    rw [show A ^ 2 + B ^ 2 = A ^ 2 * (1 + (B / A) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
  have hs1 : 0 < Real.sqrt (1 + (B / A) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos θ = 1 / Real.sqrt (1 + (B / A) ^ 2) := Real.cos_arctan _
  have hsin : Real.sin θ = B / A / Real.sqrt (1 + (B / A) ^ 2) := Real.sin_arctan _
  have hexp : exp (-(θ : ℂ) * I) = ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * I := by
    rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hexp, hcos, hsin, hsq]
  apply Complex.ext <;> simp <;> field_simp

/-! ### The data of the partial products -/

/-- `δ = (b - a)/2`. -/
noncomputable def dl (a b : ℝ) : ℝ := (b - a) / 2

/-- `c_j = j + 1/4`. -/
noncomputable def cj (j : ℕ) : ℝ := j + 1 / 4

/-- `A_j = c_j² + ab/4`, the real part of `(z + j)(w + j)`. -/
noncomputable def Aj (a b : ℝ) (j : ℕ) : ℝ := cj j ^ 2 + a * b / 4

/-- The phase contributed by the `j`-th factor. -/
noncomputable def psi (a b : ℝ) (j : ℕ) : ℝ := Real.arctan (dl a b * cj j / Aj a b j)

/-- The modulus of the `j`-th factor. -/
noncomputable def rj (a b : ℝ) (j : ℕ) : ℝ := Real.sqrt (Aj a b j ^ 2 + (dl a b * cj j) ^ 2)

/-- The partial phase `φ_n = δ log π - δ log n + Σ_{j ≤ n} ψ_j`. -/
noncomputable def phi (a b : ℝ) (n : ℕ) : ℝ :=
  dl a b * Real.log Real.pi - dl a b * Real.log n + ∑ j ∈ range (n + 1), psi a b j

/-- `z = 1/4 + ia/2`, half of `1/2 + ia`. -/
noncomputable def zA (a : ℝ) : ℂ := 1 / 4 + ((a / 2 : ℝ) : ℂ) * I

/-- `w = 1/4 - ib/2`, the conjugate of half of `1/2 + ib`. -/
noncomputable def wB (b : ℝ) : ℂ := 1 / 4 - ((b / 2 : ℝ) : ℂ) * I

/-- The constant `π^{-1/2 + iδ}`, written as an exponential. -/
noncomputable def cpi (a b : ℝ) : ℂ :=
  exp ((Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I))

lemma cj_pos (j : ℕ) : 0 < cj j := by unfold cj; positivity

lemma Aj_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) : 0 < Aj a b j := by
  unfold Aj; have := cj_pos j; positivity

lemma zA_re (a : ℝ) : (zA a).re = 1 / 4 := by simp [zA]

lemma wB_re (b : ℝ) : (wB b).re = 1 / 4 := by simp [wB]

/-- `(z + j)(w + j) = A_j - i δ c_j`. -/
lemma factor_eq (a b : ℝ) (j : ℕ) :
    (zA a + j) * (wB b + j) = (Aj a b j : ℂ) - ((dl a b * cj j : ℝ) : ℂ) * I := by
  unfold zA wB Aj dl cj
  push_cast
  linear_combination (-(a : ℂ) * b / 4) * Complex.I_sq

/-- Each factor in polar form. -/
lemma factor_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) :
    (zA a + j) * (wB b + j) = (rj a b j : ℂ) * exp (-(psi a b j : ℂ) * I) := by
  rw [factor_eq]
  exact polar_of_re_pos (Aj_pos ha hb j)

/-- The product of the factors in polar form. -/
lemma prod_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (∏ j ∈ range (n + 1), (zA a + j)) * (∏ j ∈ range (n + 1), (wB b + j))
      = ((∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
        * exp (-(((∑ j ∈ range (n + 1), psi a b j : ℝ)) : ℂ) * I) := by
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun j _ => factor_polar ha hb j),
    Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]

/-- `n^z n^w = exp(log n · (1/2 - iδ))` for `n ≥ 1`. -/
lemma cpow_pair {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    (n : ℂ) ^ zA a * (n : ℂ) ^ wB b
      = exp ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← cpow_add _ _ hn', cpow_def_of_ne_zero hn', ← Complex.natCast_log]
  congr 1
  unfold zA wB dl
  push_cast
  ring

/-- The partial product `V_n = π^{-1/2+iδ} GammaSeq z n · GammaSeq w n`. -/
noncomputable def Vn (a b : ℝ) (n : ℕ) : ℂ :=
  cpi a b * (GammaSeq (zA a) n * GammaSeq (wB b) n)

lemma factor_ne_zero_A (a : ℝ) (j : ℕ) : zA a + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [zA] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

lemma factor_ne_zero_B (b : ℝ) (j : ℕ) : wB b + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [wB] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- **`V_n` in polar form**: a positive real times `exp(x + iφ_n)`. -/
lemma Vn_polar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    Vn a b n = (((n.factorial : ℝ) ^ 2 / ∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
      * exp (((Real.log n - Real.log Real.pi) / 2 : ℝ) + (phi a b n : ℂ) * I) := by
  have hPA : (∏ j ∈ range (n + 1), (zA a + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero_A a j
  have hPB : (∏ j ∈ range (n + 1), (wB b + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero_B b j
  have hr : (((∏ j ∈ range (n + 1), rj a b j : ℝ)) : ℂ) ≠ 0 := by
    have hpp := prod_polar ha hb n
    intro h0
    rw [h0, zero_mul] at hpp
    exact mul_ne_zero hPA hPB hpp
  have hsplit : Vn a b n
      = cpi a b * ((n : ℂ) ^ zA a * (n : ℂ) ^ wB b) * ((n.factorial : ℂ) ^ 2)
        / ((∏ j ∈ range (n + 1), (zA a + j)) * (∏ j ∈ range (n + 1), (wB b + j))) := by
    unfold Vn GammaSeq
    field_simp
  rw [hsplit, cpow_pair hn, prod_polar ha hb n]
  have hE : ((((Real.log n - Real.log Real.pi) / 2 : ℝ) : ℂ) + (phi a b n : ℂ) * I)
      = (Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I)
        + ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I)
        + ((∑ j ∈ range (n + 1), psi a b j : ℝ) : ℂ) * I) := by
    unfold phi
    push_cast
    ring
  rw [hE, Complex.exp_add, Complex.exp_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  unfold cpi
  set X := exp ((Real.log Real.pi : ℂ) * (-(1 / 2) + (dl a b : ℂ) * I))
  set Y := exp ((Real.log n : ℂ) * (1 / 2 - (dl a b : ℂ) * I))
  set Θ : ℂ := ((∑ j ∈ range (n + 1), psi a b j : ℝ) : ℂ)
  set P : ℂ := ((∏ j ∈ range (n + 1), rj a b j : ℝ) : ℂ)
  have hinv : exp (Θ * I) = (exp (-Θ * I))⁻¹ := by
    rw [← Complex.exp_neg, neg_mul, neg_neg]
  have hne : exp (-Θ * I) ≠ 0 := Complex.exp_ne_zero _
  rw [hinv]
  field_simp

/-- `Re (R e^{x + iy}) = ‖R e^{x + iy}‖ cos y` for `R ≥ 0`. -/
lemma re_eq_norm_mul_cos {R : ℝ} (hR : 0 ≤ R) (x y : ℝ) :
    ((R : ℂ) * exp ((x : ℂ) + (y : ℂ) * I)).re
      = ‖(R : ℂ) * exp ((x : ℂ) + (y : ℂ) * I)‖ * Real.cos y := by
  rw [Complex.re_ofReal_mul, Complex.exp_re, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hR]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  ring

lemma Vn_re {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    (Vn a b n).re = ‖Vn a b n‖ * Real.cos (phi a b n) := by
  have hR : 0 ≤ (n.factorial : ℝ) ^ 2 / ∏ j ∈ range (n + 1), rj a b j :=
    div_nonneg (by positivity)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _)
  rw [Vn_polar ha hb hn]
  exact re_eq_norm_mul_cos hR _ _

/-! ### Elementary bounds on the partial phase -/

lemma arctan_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 ≤ Real.arctan x := by
  have h1 : Real.sin (Real.arctan x) ≤ Real.arctan x :=
    Real.sin_le (Real.arctan_nonneg.mpr hx)
  rw [Real.sin_arctan] at h1
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hs : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by nlinarith [sq_nonneg x]))
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hpos
  have h2 : x / (1 + x ^ 2) ≤ x / Real.sqrt (1 + x ^ 2) :=
    div_le_div_of_nonneg_left hx hspos hs
  have h3 : x - x ^ 3 ≤ x / (1 + x ^ 2) := by
    rw [le_div_iff₀ hpos]
    nlinarith [pow_nonneg hx 5, sq_nonneg x]
  linarith

/-- `x_j = δ c_j / A_j`, the argument of the `j`-th arctangent. -/
noncomputable def xj (a b : ℝ) (j : ℕ) : ℝ := dl a b * cj j / Aj a b j

lemma xj_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : 0 ≤ xj a b j := by
  unfold xj dl
  have := Aj_pos ha (ha.trans hab) j
  have := cj_pos j
  have : 0 ≤ b - a := by linarith
  positivity

lemma xj_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : xj a b j ≤ dl a b / cj j := by
  have hc := cj_pos j
  have hA := Aj_pos ha (ha.trans hab) j
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  unfold xj
  rw [div_le_div_iff₀ hA hc]
  have : cj j ^ 2 ≤ Aj a b j := by
    unfold Aj; have : 0 ≤ a * b := mul_nonneg ha (ha.trans hab); linarith
  nlinarith

/-- `x_j ≥ δ (1/c_j - K/c_j³)`. -/
lemma xj_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) :
    dl a b * (1 / cj j - (a * b / 4) / cj j ^ 3) ≤ xj a b j := by
  have hc := cj_pos j
  have hA := Aj_pos ha (ha.trans hab) j
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  have hx : xj a b j = dl a b * (cj j / Aj a b j) := by unfold xj; ring
  rw [hx]
  refine mul_le_mul_of_nonneg_left ?_ hd
  have hA' : Aj a b j = cj j ^ 2 + a * b / 4 := rfl
  have he : 1 / cj j - (a * b / 4) / cj j ^ 3 = (cj j ^ 2 - a * b / 4) / cj j ^ 3 := by
    field_simp
  rw [he, div_le_div_iff₀ (pow_pos hc 3) hA, hA']
  nlinarith [sq_nonneg (a * b / 4), pow_pos hc 4]

lemma psi_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) : psi a b j ≤ xj a b j :=
  Real.arctan_le_self (xj_nonneg ha hab j)

lemma psi_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (j : ℕ) :
    xj a b j - xj a b j ^ 3 ≤ psi a b j :=
  arctan_ge_sub_cube (xj_nonneg ha hab j)

/-- `Σ_{j<n} 1/(j+1)² ≤ 2`, in the form the induction wants. -/
lemma sum_inv_sq_le_aux (n : ℕ) :
    ∑ j ∈ range (n + 1), 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have key : 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2
        ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at key ⊢
    linarith

lemma sum_inv_sq_le (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases n with _ | n
  · simp
  · have := sum_inv_sq_le_aux n
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- `Σ_{j ≤ n} 1/c_j ≤ 5 + log n`. -/
lemma sum_inv_cj_le (n : ℕ) : ∑ j ∈ range (n + 1), 1 / cj j ≤ 5 + Real.log n := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cj 0 = 4 := by unfold cj; norm_num
  have hterm : ∀ j ∈ range n, 1 / cj (j + 1) ≤ 1 / ((j : ℝ) + 1) := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) = (harmonic n : ℝ) := by
    simp [harmonic]
  have := harmonic_le_one_add_log n
  have := Finset.sum_le_sum hterm
  rw [h0]
  linarith

/-- `Σ_{j ≤ n} 1/c_j³ ≤ 66`. -/
lemma sum_inv_cj_cube_le (n : ℕ) : ∑ j ∈ range (n + 1), 1 / cj j ^ 3 ≤ 66 := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / cj 0 ^ 3 = 64 := by unfold cj; norm_num
  have hterm : ∀ j ∈ range n, 1 / cj (j + 1) ^ 3 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    have h2 : (j : ℝ) + 1 ≤ (j : ℝ) + 1 + 1 / 4 := by linarith
    calc ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 := by
          nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 3 by norm_num)]
      _ ≤ ((j : ℝ) + 1 + 1 / 4) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
  have := Finset.sum_le_sum hterm
  have := sum_inv_sq_le n
  rw [h0]
  linarith

/-- `Σ_{j<n} 1/c_{j+1} ≥ log n - 1` for `n ≥ 1`. -/
lemma sum_inv_cj_succ_ge {n : ℕ} (hn : n ≠ 0) :
    Real.log n - 1 ≤ ∑ j ∈ range n, 1 / cj (j + 1) := by
  have hterm : ∀ j ∈ range n, 1 / ((j : ℝ) + 2) ≤ 1 / cj (j + 1) := by
    intro j _
    unfold cj
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : (harmonic (n + 1) : ℝ) = 1 + ∑ j ∈ range n, 1 / ((j : ℝ) + 2) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [Finset.sum_range_succ']
    push_cast
    rw [add_comm]
    congr 1
    · norm_num
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_div]
      ring_nf
  have hlog := log_add_one_le_harmonic (n + 1)
  have hmono : Real.log n ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have := Finset.sum_le_sum hterm
  push_cast at hlog hmono
  linarith

/-- **Upper end of the window**: `φ_n ≤ δ(log π + 5)`. -/
lemma phi_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    phi a b n ≤ dl a b * (Real.log Real.pi + 5) := by
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have h1 : ∑ j ∈ range (n + 1), psi a b j ≤ ∑ j ∈ range (n + 1), dl a b * (1 / cj j) :=
    Finset.sum_le_sum fun j _ =>
      (psi_le ha hab j).trans ((xj_le ha hab j).trans (by rw [mul_one_div]))
  rw [← Finset.mul_sum] at h1
  have h2 := mul_le_mul_of_nonneg_left (sum_inv_cj_le n) hd
  unfold phi
  nlinarith

/-- **Lower end of the window**: `φ_n ≥ δ(log π - 1 - 2K) - 66 δ³` for `n ≥ 1`. -/
lemma le_phi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {n : ℕ} (hn : n ≠ 0) :
    dl a b * (Real.log Real.pi - 1 - 2 * (a * b / 4)) - 66 * dl a b ^ 3 ≤ phi a b n := by
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  -- the arctangents against the linear terms, minus the cubes
  have h1 : ∑ j ∈ range (n + 1), (xj a b j - xj a b j ^ 3) ≤ ∑ j ∈ range (n + 1), psi a b j :=
    Finset.sum_le_sum fun j _ => psi_ge ha hab j
  rw [Finset.sum_sub_distrib] at h1
  -- the cubes
  have h2 : ∑ j ∈ range (n + 1), xj a b j ^ 3 ≤ dl a b ^ 3 * 66 := by
    have : ∀ j ∈ range (n + 1), xj a b j ^ 3 ≤ dl a b ^ 3 * (1 / cj j ^ 3) := by
      intro j _
      have hx := xj_le ha hab j
      have hx0 := xj_nonneg ha hab j
      calc xj a b j ^ 3 ≤ (dl a b / cj j) ^ 3 := pow_le_pow_left₀ hx0 hx 3
        _ = dl a b ^ 3 * (1 / cj j ^ 3) := by rw [div_pow]; ring
    calc ∑ j ∈ range (n + 1), xj a b j ^ 3
        ≤ ∑ j ∈ range (n + 1), dl a b ^ 3 * (1 / cj j ^ 3) := Finset.sum_le_sum this
      _ = dl a b ^ 3 * ∑ j ∈ range (n + 1), 1 / cj j ^ 3 := by rw [Finset.mul_sum]
      _ ≤ dl a b ^ 3 * 66 :=
          mul_le_mul_of_nonneg_left (sum_inv_cj_cube_le n) (pow_nonneg hd 3)
  -- the linear terms, dropping `j = 0`
  have h3 : ∑ j ∈ range n, xj a b (j + 1) ≤ ∑ j ∈ range (n + 1), xj a b j := by
    rw [Finset.sum_range_succ' (fun j => xj a b j)]
    linarith [xj_nonneg ha hab 0]
  have h4 : ∑ j ∈ range n, dl a b * (1 / cj (j + 1) - (a * b / 4) / cj (j + 1) ^ 3)
      ≤ ∑ j ∈ range n, xj a b (j + 1) :=
    Finset.sum_le_sum fun j _ => xj_ge ha hab (j + 1)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h4
  have h5 : ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3 ≤ (a * b / 4) * 2 := by
    have : ∀ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3 ≤ (a * b / 4) * (1 / ((j : ℝ) + 1) ^ 2) := by
      intro j _
      rw [div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hK
      unfold cj
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      have h1' : (1 : ℝ) ≤ (j : ℝ) + 1 := by
        have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      calc ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 := by
            nlinarith [pow_le_pow_right₀ h1' (show 2 ≤ 3 by norm_num)]
        _ ≤ ((j : ℝ) + 1 + 1 / 4) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3
        ≤ ∑ j ∈ range n, (a * b / 4) * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum this
      _ = (a * b / 4) * ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (a * b / 4) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le n) hK
  have h6 := sum_inv_cj_succ_ge hn
  have h7 : dl a b * (Real.log n - 1 - (a * b / 4) * 2)
      ≤ dl a b * (∑ j ∈ range n, 1 / cj (j + 1) - ∑ j ∈ range n, (a * b / 4) / cj (j + 1) ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hd
  unfold phi
  nlinarith

/-! ### From the partial products to `Γℝ` -/

lemma sOf_half (t : ℝ) : sOf t / 2 = zA t := by
  unfold sOf zA; push_cast; ring

lemma conj_sOf_half (t : ℝ) : conj (sOf t / 2) = wB t := by
  unfold sOf wB
  rw [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    map_div₀, map_one, map_ofNat]
  push_cast
  ring

/-- `Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib) = π^{-1/2 + iδ} Γ(z) Γ(w)`. -/
lemma gammaR_prod (a b : ℝ) :
    Gammaℝ (sOf a) * conj (Gammaℝ (sOf b)) = cpi a b * (Gamma (zA a) * Gamma (wB b)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlog : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, sOf_half, conj_sOf_half,
    cpow_def_of_ne_zero hpi, cpow_def_of_ne_zero hpi, hlog, ← Complex.exp_conj]
  have hc : exp ((Real.log Real.pi : ℂ) * (-sOf a / 2))
      * exp (conj ((Real.log Real.pi : ℂ) * (-sOf b / 2))) = cpi a b := by
    rw [← Complex.exp_add]
    unfold cpi
    congr 1
    rw [map_mul, Complex.conj_ofReal, map_div₀, map_neg, map_ofNat]
    unfold sOf dl
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    ring
  rw [← hc]
  ring

lemma tendsto_Vn (a b : ℝ) :
    Tendsto (Vn a b) atTop (𝓝 (cpi a b * (Gamma (zA a) * Gamma (wB b)))) :=
  ((GammaSeq_tendsto_Gamma _).mul (GammaSeq_tendsto_Gamma _)).const_mul _

/-- **The phase lemma.** If the explicit window `[-L, L]` with `L < π/2` holds the
two ends of the partial-phase bounds, the product of the two `Γℝ` values has
positive real part. No value of `Γ` is used. -/
theorem gammaR_re_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {L : ℝ}
    (hL : L < Real.pi / 2)
    (hup : dl a b * (Real.log Real.pi + 5) ≤ L)
    (hlo : -L ≤ dl a b * (Real.log Real.pi - 1 - 2 * (a * b / 4)) - 66 * dl a b ^ 3) :
    0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re := by
  rw [gammaR_prod]
  set V := cpi a b * (Gamma (zA a) * Gamma (wB b)) with hVdef
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hL0 : 0 ≤ L := le_trans (mul_nonneg hd (by linarith)) hup
  have hcosL : 0 < Real.cos L :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hL⟩
  have hev : ∀ᶠ n in atTop, Real.cos L * ‖Vn a b n‖ ≤ (Vn a b n).re := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : n ≠ 0 := by omega
    rw [Vn_re ha (ha.trans hab) hn0]
    have hphi : |phi a b n| ≤ L :=
      abs_le.mpr ⟨hlo.trans (le_phi ha hab hn0), (phi_le ha hab n).trans hup⟩
    have hcos : Real.cos L ≤ Real.cos (phi a b n) := by
      rw [← Real.cos_abs (phi a b n)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) hphi
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
  have hlim := tendsto_Vn a b
  have hre : Tendsto (fun n => (Vn a b n).re) atTop (𝓝 V.re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have hnorm : Tendsto (fun n => Real.cos L * ‖Vn a b n‖) atTop (𝓝 (Real.cos L * ‖V‖)) :=
    hlim.norm.const_mul _
  have hle : Real.cos L * ‖V‖ ≤ V.re := le_of_tendsto_of_tendsto hnorm hre hev
  have hV : V ≠ 0 := by
    refine mul_ne_zero (by unfold cpi; exact Complex.exp_ne_zero _) (mul_ne_zero ?_ ?_)
    · exact Gamma_ne_zero_of_re_pos (by rw [zA_re]; norm_num)
    · exact Gamma_ne_zero_of_re_pos (by rw [wB_re]; norm_num)
  have : 0 < Real.cos L * ‖V‖ := mul_pos hcosL (norm_pos_iff.mpr hV)
  linarith



end HardyFirstZero


/- SOURCE: hunts/hardy_first_zero/lean/HardyFirstZero/EulerMaclaurin.lean -/
open intervalIntegral MeasureTheory Complex

namespace HardyFirstZero

/-- The quartic kernel on `[a, a+1]` and its first three derivatives. -/
noncomputable def kq (a t : ℝ) : ℝ := (t - a) ^ 2 * (a + 1 - t) ^ 2 / 24
noncomputable def kq1 (a t : ℝ) : ℝ := (t - a) * (a + 1 - t) * (2 * a + 1 - 2 * t) / 12
noncomputable def kq2 (a t : ℝ) : ℝ := (1 - 6 * (t - a) + 6 * (t - a) ^ 2) / 12
noncomputable def kq3 (a t : ℝ) : ℝ := (t - a) - 1 / 2

lemma hasDerivAt_kq (a t : ℝ) : HasDerivAt (kq a) (kq1 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => a + 1 - x) (-1) t := (hasDerivAt_id' t).const_sub (a + 1)
  have h := ((h1.fun_pow 2).fun_mul (h2.fun_pow 2)).div_const 24
  unfold kq kq1
  convert h using 1 <;> try rfl
  push_cast
  ring

lemma hasDerivAt_kq1 (a t : ℝ) : HasDerivAt (kq1 a) (kq2 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h2 : HasDerivAt (fun x : ℝ => a + 1 - x) (-1) t := (hasDerivAt_id' t).const_sub (a + 1)
  have h3 : HasDerivAt (fun x : ℝ => 2 * a + 1 - 2 * x) (-(2 * 1)) t :=
    ((hasDerivAt_id' t).const_mul 2).const_sub (2 * a + 1)
  have h := ((h1.fun_mul h2).fun_mul h3).div_const 12
  unfold kq1 kq2
  convert h using 1 <;> try rfl
  ring

lemma hasDerivAt_kq2 (a t : ℝ) : HasDerivAt (kq2 a) (kq3 a t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have h := (((h1.const_mul 6).const_sub 1).fun_add ((h1.fun_pow 2).const_mul 6)).div_const 12
  unfold kq2 kq3
  convert h using 1 <;> try rfl
  push_cast
  ring

lemma hasDerivAt_kq3 (a t : ℝ) : HasDerivAt (kq3 a) 1 t :=
  ((hasDerivAt_id' t).sub_const a).sub_const (1 / 2 : ℝ)

lemma kq_nonneg (a t : ℝ) : 0 ≤ kq a t := by unfold kq; positivity

lemma integral_kq (a : ℝ) : ∫ t in a..a + 1, kq a t = 1 / 720 := by
  have hQ : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt
      (fun t => ((t - a) ^ 3 / 3 - (t - a) ^ 4 / 2 + (t - a) ^ 5 / 5) / 24) (kq a t) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
    have h := ((((h1.fun_pow 3).div_const 3).sub ((h1.fun_pow 4).div_const 2)).add
      ((h1.fun_pow 5).div_const 5)).div_const 24
    convert h using 1 <;> try rfl
    simp only [kq]; push_cast; ring
  rw [integral_eq_sub_of_hasDerivAt hQ
    ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_kq a t).continuousAt).intervalIntegrable _ _)]
  norm_num

/-- **The corrected trapezoid rule.** For a `C⁴` function on `[a, a+1]` whose fourth
derivative is bounded by `M`, the endpoint average corrected by the first
Bernoulli term misses the integral by at most `M/720`. -/
theorem corrected_trapezoid {g g1 g2 g3 g4 : ℝ → ℂ} {a M : ℝ}
    (h0 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g (g1 t) t)
    (h1 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g1 (g2 t) t)
    (h2 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g2 (g3 t) t)
    (h3 : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt g3 (g4 t) t)
    (hc : ContinuousOn g4 (Set.uIcc a (a + 1)))
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖g4 t‖ ≤ M) :
    ‖(∫ t in a..a + 1, g t) - ((g a + g (a + 1)) / 2 - (g1 (a + 1) - g1 a) / 12)‖
      ≤ M / 720 := by
  have hab : a ≤ a + 1 := by linarith
  have hcg : ContinuousOn g (Set.uIcc a (a + 1)) := fun t ht =>
    (h0 t ht).continuousAt.continuousWithinAt
  have hck : Continuous fun t => ((kq a t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_kq a t).continuousAt)
  -- the one fundamental-theorem step
  have hF : ∀ t ∈ Set.uIcc a (a + 1), HasDerivAt
      (fun t => ((kq a t : ℝ) : ℂ) * g3 t - ((kq1 a t : ℝ) : ℂ) * g2 t
        + ((kq2 a t : ℝ) : ℂ) * g1 t - ((kq3 a t : ℝ) : ℂ) * g t)
      (((kq a t : ℝ) : ℂ) * g4 t - g t) t := by
    intro t ht
    have e0 := (hasDerivAt_kq a t).ofReal_comp.mul (h3 t ht)
    have e1 := (hasDerivAt_kq1 a t).ofReal_comp.mul (h2 t ht)
    have e2 := (hasDerivAt_kq2 a t).ofReal_comp.mul (h1 t ht)
    have e3 := (hasDerivAt_kq3 a t).ofReal_comp.mul (h0 t ht)
    convert ((e0.sub e1).add e2).sub e3 using 1 <;> try rfl
    push_cast
    ring
  have hint : IntervalIntegrable (fun t => ((kq a t : ℝ) : ℂ) * g4 t - g t) volume a (a + 1) :=
    ((hck.continuousOn.mul hc).sub hcg).intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt hF hint
  have hkg : IntervalIntegrable (fun t => ((kq a t : ℝ) : ℂ) * g4 t) volume a (a + 1) :=
    (hck.continuousOn.mul hc).intervalIntegrable
  rw [integral_sub hkg hcg.intervalIntegrable] at hftc
  have hend : ((kq a (a + 1) : ℝ) : ℂ) = 0 ∧ ((kq1 a (a + 1) : ℝ) : ℂ) = 0
      ∧ ((kq2 a (a + 1) : ℝ) : ℂ) = 1 / 12 ∧ ((kq3 a (a + 1) : ℝ) : ℂ) = 1 / 2
      ∧ ((kq a a : ℝ) : ℂ) = 0 ∧ ((kq1 a a : ℝ) : ℂ) = 0
      ∧ ((kq2 a a : ℝ) : ℂ) = 1 / 12 ∧ ((kq3 a a : ℝ) : ℂ) = -1 / 2 := by
    simp only [kq, kq1, kq2, kq3]; push_cast; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hend
  simp only [e1, e2, e3, e4, e5, e6, e7, e8] at hftc
  have hkey : (∫ t in a..a + 1, g t) - ((g a + g (a + 1)) / 2 - (g1 (a + 1) - g1 a) / 12)
      = ∫ t in a..a + 1, ((kq a t : ℝ) : ℂ) * g4 t := by
    linear_combination (-1 : ℂ) * hftc
  rw [hkey]
  calc ‖∫ t in a..a + 1, ((kq a t : ℝ) : ℂ) * g4 t‖
      ≤ ∫ t in a..a + 1, ‖((kq a t : ℝ) : ℂ) * g4 t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..a + 1, kq a t * M := by
        refine intervalIntegral.integral_mono_on hab hkg.norm ?_ fun t ht => ?_
        · exact ((continuous_iff_continuousAt.mpr fun t =>
            (hasDerivAt_kq a t).continuousAt).mul continuous_const).intervalIntegrable _ _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kq_nonneg a t)]
          exact mul_le_mul_of_nonneg_left (hM t ht) (kq_nonneg a t)
    _ = M / 720 := by
        rw [intervalIntegral.integral_mul_const, integral_kq]
        ring

/-! ### The zeta block -/

/-- The order-4 block on `[x, x+1]`: the integral of `t^{-s}` minus its corrected
trapezoid, in closed form. -/
noncomputable def eBlock (s : ℂ) (x : ℝ) : ℂ :=
  (((x + 1 : ℝ) : ℂ) ^ (1 - s) - ((x : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
    - (((x : ℝ) : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) / 2
    - s / 12 * (((x + 1 : ℝ) : ℂ) ^ (-s - 1) - ((x : ℝ) : ℂ) ^ (-s - 1))

/-- `P(s) = s(s+1)(s+2)(s+3)`, the constant of the fourth derivative of `t^{-s}`. -/
noncomputable def P4 (s : ℂ) : ℂ := s * (s + 1) * (s + 2) * (s + 3)

private lemma ne_zero_of_re_neg {r : ℂ} (h : r.re < 0) : r ≠ 0 := by
  rintro rfl; simp at h

/-- **The block bound**: `‖e(s, x)‖ ≤ ‖P(s)‖ x^{-σ-4} / 720` for `x ≥ 1`, `Re s > 0`, `s ≠ 1`. -/
theorem norm_eBlock_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖eBlock s x‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := by
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ Set.uIcc x (x + 1), 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    linarith [ht.1]
  have r0 : (-s : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r1 : (-s - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r2 : (-s - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have r3 : (-s - 1 - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  set g1 : ℝ → ℂ := fun t => -s * (t : ℂ) ^ (-s - 1)
  set g2 : ℝ → ℂ := fun t => -s * (-s - 1) * (t : ℂ) ^ (-s - 1 - 1)
  set g3 : ℝ → ℂ := fun t => -s * (-s - 1) * (-s - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1)
  set g4 : ℝ → ℂ := fun t =>
    -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1 - 1)
  have d0 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g (g1 t) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r0
  have d1 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g1 (g2 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r1).const_mul (-s)
    convert this using 1 <;> try rfl
    simp only [g2]; ring
  have d2 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g2 (g3 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r2).const_mul (-s * (-s - 1))
    convert this using 1 <;> try rfl
    simp only [g3]; ring
  have d3 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g3 (g4 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r3).const_mul
      (-s * (-s - 1) * (-s - 1 - 1))
    convert this using 1 <;> try rfl
    simp only [g4]; ring
  have r4 : (-s - 1 - 1 - 1 - 1 : ℂ) ≠ 0 := ne_zero_of_re_neg (by simp; linarith)
  have hc4 : ContinuousOn g4 (Set.uIcc x (x + 1)) := fun t ht =>
    ((hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r4).continuousAt.const_mul
      _).continuousWithinAt
  have hM : ∀ t ∈ Set.Icc x (x + 1), ‖g4 t‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [g4]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hP : ‖-s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1)‖ = ‖P4 s‖ := by
      rw [show -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) = P4 s by unfold P4; ring]
    rw [hP]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (-s - 1 - 1 - 1 - 1).re = -s.re - 4 := by simp; ring
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos hx0 ht.1 (by linarith)
  have hT := corrected_trapezoid d0 d1 d2 d3 hc4 hM
  -- the integral in closed form
  have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := fun h => (lt_irrefl 0) (hpos 0 h)
  have hI : ∫ t in x..x + 1, g t
      = ((((x + 1 : ℝ) : ℂ) ^ (-s + 1) - ((x : ℝ) : ℂ) ^ (-s + 1)) / (-s + 1)) := by
    simp only [g]
    rw [integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), h0⟩)]
  have hE : eBlock s x
      = (∫ t in x..x + 1, g t) - ((g x + g (x + 1)) / 2 - (g1 (x + 1) - g1 x) / 12) := by
    rw [hI]
    simp only [eBlock, g, g1]
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    push_cast
    ring
  rw [hE]
  calc _ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := hT
    _ = _ := rfl

/-! ### The representation where everything converges: `Re s > 2` -/

/-- The block at a natural point, written with natural-number casts. -/
lemma eBlock_nat (s : ℂ) (n : ℕ) :
    eBlock s (n : ℝ)
      = (((n + 1 : ℕ) : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)
        - ((n : ℂ) ^ (-s) + ((n + 1 : ℕ) : ℂ) ^ (-s)) / 2
        - s / 12 * (((n + 1 : ℕ) : ℂ) ^ (-s - 1) - (n : ℂ) ^ (-s - 1)) := by
  simp only [eBlock]
  push_cast
  ring

/-- The shifted Dirichlet series `Σ_k (k + N)^{-w}`, for `Re w > 1`. -/
lemma hasSum_shift {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) := Complex.summable_one_div_nat_cpow.mpr hw
  have h : HasSum (fun n : ℕ => (n : ℂ) ^ (-w)) (riemannZeta w) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw]
    convert hsum.hasSum using 1
    funext n; rw [Complex.cpow_neg, one_div]
  exact (hasSum_nat_add_iff' N).mpr h

/-- The same series with one more shift. -/
lemma hasSum_shift_succ {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + 1 + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w) - (N : ℂ) ^ (-w)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_shift hw N)
  simpa [Finset.sum_range_one, add_comm, add_left_comm, add_assoc] using h

/-- **The order-4 representation on `Re s > 2`**, by absolute convergence. -/
theorem zeta_em4_of_two_lt {s : ℂ} (hs : 2 < s.re) (N : ℕ) :
    riemannZeta s
      = ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
        - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ) := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have h1s : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hA := hasSum_shift (w := s) (by linarith) N
  have hA1 := hasSum_shift_succ (w := s) (by linarith) N
  have hC := hasSum_shift (w := s - 1) (by simp; linarith) N
  have hC1 := hasSum_shift_succ (w := s - 1) (by simp; linarith) N
  have hD := hasSum_shift (w := s + 1) (by simp; linarith) N
  have hD1 := hasSum_shift_succ (w := s + 1) (by simp; linarith) N
  have hE := (((hC1.sub hC).div_const (1 - s)).sub ((hA.add hA1).div_const 2)).sub
    ((hD1.sub hD).mul_left (s / 12))
  have hfun : (fun k : ℕ => eBlock s ((k + N : ℕ) : ℝ))
      = fun k : ℕ =>
        (((k + 1 + N : ℕ) : ℂ) ^ (-(s - 1)) - ((k + N : ℕ) : ℂ) ^ (-(s - 1))) / (1 - s)
        - (((k + N : ℕ) : ℂ) ^ (-s) + ((k + 1 + N : ℕ) : ℂ) ^ (-s)) / 2
        - s / 12 * (((k + 1 + N : ℕ) : ℂ) ^ (-(s + 1)) - ((k + N : ℕ) : ℂ) ^ (-(s + 1))) := by
    funext k
    rw [eBlock_nat]
    have e1 : (k + N + 1 : ℕ) = k + 1 + N := by omega
    rw [e1, show (-(s - 1) : ℂ) = 1 - s by ring, show (-(s + 1) : ℂ) = -s - 1 by ring]
  rw [← hfun] at hE
  rw [hE.tsum_eq]
  rw [show (-(s - 1) : ℂ) = 1 - s by ring, show (-(s + 1) : ℂ) = -s - 1 by ring]
  field_simp
  ring

/-! ### Continuation to the quarter plane `Re s > 0, Im s > 0` -/

/-- The right side of the representation, as a function of `s`. -/
noncomputable def emRHS (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
    + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
    - ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)

/-- The open quarter plane; it contains the critical line above the axis and
avoids the pole at `1`. -/
def QP : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}

lemma isOpen_QP : IsOpen QP :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma convex_QP : Convex ℝ QP := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => Complex.add_re x y, fun c x => by simp [Complex.real_smul, Complex.mul_re]⟩
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun x y => Complex.add_im x y, fun c x => by simp [Complex.real_smul, Complex.mul_im]⟩
  exact (convex_halfSpace_gt hre 0).inter (convex_halfSpace_gt him 0)

lemma ne_one_of_QP {z : ℂ} (hz : z ∈ QP) : z ≠ 1 := by
  rintro rfl; simp [QP] at hz

lemma differentiableAt_eBlock {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (fun w => eBlock w x) s := by
  have hb0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hb1 : ((x + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hl : DifferentiableAt ℂ (fun w : ℂ => 1 - w) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hn1 : DifferentiableAt ℂ (fun w : ℂ => -w - 1) s := hn.sub (differentiableAt_const _)
  unfold eBlock
  refine (((hl.const_cpow (Or.inl hb1)).sub (hl.const_cpow (Or.inl hb0))).div hl
    (sub_ne_zero.mpr (Ne.symm hs))).sub
    (((hn.const_cpow (Or.inl hb0)).add (hn.const_cpow (Or.inl hb1))).div_const 2) |>.sub
    ((differentiableAt_id.div_const 12).mul
      ((hn1.const_cpow (Or.inl hb1)).sub (hn1.const_cpow (Or.inl hb0))))

private lemma summable_shift_rpow {p : ℝ} (hp : 1 < p) (N : ℕ) :
    Summable (fun k : ℕ => (((k + N : ℕ) : ℝ)) ^ (-p)) := by
  have hbase : Summable (fun k : ℕ => ((k : ℝ)) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff (f := fun k : ℕ => ((k : ℝ)) ^ (-p)) N).mpr hbase |>.congr
    fun k => by push_cast; ring_nf

lemma differentiableOn_tail {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableOn ℂ (fun s => ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)) QP := by
  intro s₀ hs₀
  obtain ⟨hre0, him0⟩ := hs₀
  set δ : ℝ := min s₀.re s₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδre : δ ≤ s₀.re / 2 := by rw [hδ]; linarith [min_le_left s₀.re s₀.im]
  have hδim : δ ≤ s₀.im / 2 := by rw [hδ]; linarith [min_le_right s₀.re s₀.im]
  have hball : ∀ w ∈ Metric.ball s₀ δ, s₀.re / 2 ≤ w.re ∧ 0 < w.im ∧ ‖w‖ ≤ ‖s₀‖ + δ := by
    intro w hw
    have hd : ‖w - s₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_re_le_norm (w - s₀)
    have h2 := Complex.abs_im_le_norm (w - s₀)
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    refine ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h2).1], ?_⟩
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + δ := by linarith
  set R : ℝ := ‖s₀‖ + δ + 3 with hR
  have hsub : Metric.ball s₀ δ ⊆ QP := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hball w hw
    exact ⟨by linarith, h2⟩
  have hu : Summable (fun k : ℕ => R ^ 4 * (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) / 720) :=
    ((summable_shift_rpow (p := s₀.re / 2 + 4) (by linarith) N).mul_left (R ^ 4)).div_const 720
  have hF_le : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s₀ δ →
      ‖eBlock w ((k + N : ℕ) : ℝ)‖ ≤ R ^ 4 * (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) / 720 := by
    intro k w hw
    obtain ⟨h1, h2, h3⟩ := hball w hw
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
      have : 1 ≤ k + N := by omega
      exact_mod_cast this
    refine (norm_eBlock_le (by linarith) (ne_one_of_QP (hsub hw)) hx1).trans ?_
    have hP : ‖P4 w‖ ≤ R ^ 4 := by
      unfold P4
      have e1 : ‖w + 1‖ ≤ R := by
        calc ‖w + 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e2 : ‖w + 2‖ ≤ R := by
        calc ‖w + 2‖ ≤ ‖w‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e3 : ‖w + 3‖ ≤ R := by
        calc ‖w + 3‖ ≤ ‖w‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
          _ ≤ R := by simp; linarith
      have e0 : ‖w‖ ≤ R := by linarith
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖w‖ * ‖w + 1‖ * ‖w + 2‖ * ‖w + 3‖ ≤ R * R * R * R := by gcongr
        _ = R ^ 4 := by ring
    have hpow : (((k + N : ℕ) : ℝ)) ^ (-w.re - 4) ≤ (((k + N : ℕ) : ℝ)) ^ (-(s₀.re / 2 + 4)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hnn : 0 ≤ (((k + N : ℕ) : ℝ)) ^ (-w.re - 4) := Real.rpow_nonneg (by linarith) _
    have := mul_le_mul hP hpow hnn (by positivity)
    linarith
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun w => eBlock w ((k + N : ℕ) : ℝ)) (Metric.ball s₀ δ) :=
    fun k w hw => (differentiableAt_eBlock (by
      have : 1 ≤ k + N := by omega
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one this))
      (ne_one_of_QP (hsub hw))).differentiableWithinAt
  have hD := differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball hF_le
  exact (hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ0))).differentiableWithinAt

lemma differentiableOn_emRHS {N : ℕ} (hN : 1 ≤ N) : DifferentiableOn ℂ (emRHS N) QP := by
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; simp [QP] at hs
  have hs1 := ne_one_of_QP hs
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hsum : DifferentiableAt ℂ (fun w => ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) s :=
    DifferentiableAt.fun_sum fun i _ => hn.const_cpow (Or.inr (neg_ne_zero.mpr hs0))
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (1 - w) / (w - 1)) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hNne)).div
      (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs1)
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (-w) / 2) s :=
    (hn.const_cpow (Or.inl hNne)).div_const 2
  have h4 : DifferentiableAt ℂ (fun w : ℂ => w / 12 * (N : ℂ) ^ (-w - 1)) s :=
    (differentiableAt_id.div_const 12).mul
      ((hn.sub (differentiableAt_const _)).const_cpow (Or.inl hNne))
  have h5 : DifferentiableAt ℂ (fun s => ∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)) s :=
    (differentiableOn_tail hN).differentiableAt (isOpen_QP.mem_nhds hs)
  exact ((((hsum.add h2).add h3).add h4).sub h5).differentiableWithinAt

/-- **The order-4 representation on the quarter plane**, by the identity theorem. -/
theorem zeta_em4 {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 1 ≤ N) : riemannZeta s = emRHS N s := by
  have hzd : DifferentiableOn ℂ riemannZeta QP := fun z hz =>
    (differentiableAt_riemannZeta (ne_one_of_QP hz)).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ riemannZeta QP := hzd.analyticOnNhd isOpen_QP
  have he : AnalyticOnNhd ℂ (emRHS N) QP := (differentiableOn_emRHS hN).analyticOnNhd isOpen_QP
  have hmem : (3 + I : ℂ) ∈ QP := by simp [QP]
  have hev : riemannZeta =ᶠ[nhds (3 + I : ℂ)] emRHS N := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp; norm_num)) fun z hz => ?_
    exact zeta_em4_of_two_lt hz N
  exact hz.eqOn_of_preconnected_of_eventuallyEq he convex_QP.isPreconnected hmem hev hs

/-! ### The tail, by the integral test -/

theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 2 ≤ N) :
    ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
  set p : ℝ := s.re + 4 with hp
  have hsumb : Summable (fun k : ℕ => (((k + N : ℕ) : ℝ)) ^ (-p)) :=
    summable_shift_rpow (by linarith) N
  have hb : ∀ k : ℕ, ‖eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720 := by
    intro k
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + N)
    have := norm_eBlock_le hs hs1 hx1
    rwa [show -s.re - 4 = -p by rw [hp]; ring] at this
  have hg : Summable (fun k : ℕ => ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720) :=
    (hsumb.mul_left _).div_const _
  have hnorm : Summable (fun k : ℕ => ‖eBlock s ((k + N : ℕ) : ℝ)‖) :=
    hg.of_nonneg_of_le (fun k => norm_nonneg _) hb
  have hKR : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-p)) (Set.Ici ((N - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hKR hx) hxy (by linarith)
  have hintg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi ((N - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hKR
  have hnonneg : ∀ t ∈ Set.Ioi ((N - 1 : ℕ) : ℝ), 0 ≤ (fun t : ℝ => t ^ (-p)) t := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt hKR.le ht)) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (N - 1) hanti hintg hnonneg
  have hidx : ∀ n : ℕ, n + (N - 1) + 1 = n + N := fun n => by omega
  simp only [hidx] at htail
  have hint : ∫ t in Set.Ioi ((N - 1 : ℕ) : ℝ), t ^ (-p)
      = ((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hKR, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one,
      show -p + 1 = -(s.re + 3) by rw [hp]; ring, neg_div_neg_eq]
    congr 1
    ring_nf
  rw [hint] at htail
  calc ‖∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ)‖
      ≤ ∑' k : ℕ, ‖eBlock s ((k + N : ℕ) : ℝ)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖P4 s‖ * (((k + N : ℕ) : ℝ)) ^ (-p) / 720 := hnorm.tsum_le_tsum hb hg
    _ = ‖P4 s‖ * (∑' k : ℕ, (((k + N : ℕ) : ℝ)) ^ (-p)) / 720 := by
        rw [tsum_div_const, tsum_mul_left]
    _ ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
        gcongr

/-- **The order-4 Euler-Maclaurin remainder for zeta**, on the quarter plane:
for `Re s > 0`, `Im s > 0` and `N ≥ 2`,

    ‖ζ(s) - (Σ_{n<N} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + s N^{-s-1}/12)‖
      ≤ ‖s(s+1)(s+2)(s+3)‖ (N-1)^{-σ-3} / (720 (σ+3)). -/
theorem zeta_em4_error {s : ℂ} (hs : s ∈ QP) {N : ℕ} (hN : 2 ≤ N) :
    ‖riemannZeta s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))‖
      ≤ ‖P4 s‖ * (((N : ℝ) - 1) ^ (-s.re - 3) / (s.re + 3)) / 720 := by
  rw [zeta_em4 hs (N := N) (by omega)]
  have h : emRHS N s - (∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1))
      = -∑' k : ℕ, eBlock s ((k + N : ℕ) : ℝ) := by
    unfold emRHS; ring
  rw [h, norm_neg]
  exact norm_tail_le hs.1 (ne_one_of_QP hs) hN

end HardyFirstZero



/- SOURCE: lean/ZetaLean/Rigor.lean -/




/-!
# Certified Interval Evaluation

Exact rational interval arithmetic with kernel-checked soundness. This is the
Lean analogue of `zeta/rigor.py`'s ball arithmetic: every operation returns an
interval **together with a proved containment lemma**, so a chain of
operations carries its enclosure by construction and nothing is ever silently
upgraded to a certificate.

Two layers:

* `Interval`: closed rational intervals `[lo, hi]` regarded as sets of reals
  via `Interval.contains`, with sound `exact` / `add` / `neg` / `sub` / `mul`.
* `ComplexInterval`: axis-aligned rational rectangles in `ℂ`, componentwise
  on `re` / `im`, with the complex product routed through the real layer via
  `Complex.mul_re` / `Complex.mul_im`.

The only genuinely mathematical step is interval multiplication: the product
of `a ∈ [xl, xu]` and `b ∈ [yl, yu]` is bounded by the four corner products,
in every sign configuration. That is `mul_corners_le` / `le_mul_corners`
below, proved once over `ℝ` and reused by both layers.

Supports Rung 3 Phase B (rigorous evaluation of Dirichlet partial sums for
the Davenport–Heilbronn certificate, `ZetaLean/DirichletEval.lean`).
-/

namespace ZetaLean

/-- Lower corner bound: if `a ∈ [xl, xu]` and `b ∈ [yl, yu]` then `a * b` is
at least the smallest of the four corner products. -/
theorem mul_corners_le {a b xl xu yl yu : ℝ}
    (hx1 : xl ≤ a) (hx2 : a ≤ xu) (hy1 : yl ≤ b) (hy2 : b ≤ yu) :
    min (min (xl * yl) (xl * yu)) (min (xu * yl) (xu * yu)) ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · -- 0 ≤ b: a * b ≥ xl * b, and xl * b is over a corner of the xl row
    refine le_trans (le_trans (min_le_left _ _) ?_)
      (mul_le_mul_of_nonneg_right hx1 hb)
    rcases le_total 0 xl with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy2 h)
  · -- b ≤ 0: a * b ≥ xu * b, and xu * b is over a corner of the xu row
    refine le_trans (le_trans (min_le_right _ _) ?_)
      (mul_le_mul_of_nonpos_right hx2 hb)
    rcases le_total 0 xu with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy2 h)

/-- Upper corner bound: if `a ∈ [xl, xu]` and `b ∈ [yl, yu]` then `a * b` is
at most the largest of the four corner products. -/
theorem le_mul_corners {a b xl xu yl yu : ℝ}
    (hx1 : xl ≤ a) (hx2 : a ≤ xu) (hy1 : yl ≤ b) (hy2 : b ≤ yu) :
    a * b ≤ max (max (xl * yl) (xl * yu)) (max (xu * yl) (xu * yu)) := by
  rcases le_total 0 b with hb | hb
  · -- 0 ≤ b: a * b ≤ xu * b, bounded by a corner of the xu row
    refine le_trans (mul_le_mul_of_nonneg_right hx2 hb)
      (le_trans ?_ (le_max_right _ _))
    rcases le_total 0 xu with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hy1 h) (le_max_left _ _)
  · -- b ≤ 0: a * b ≤ xl * b, bounded by a corner of the xl row
    refine le_trans (mul_le_mul_of_nonpos_right hx1 hb)
      (le_trans ?_ (le_max_left _ _))
    rcases le_total 0 xl with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left hy2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hy1 h) (le_max_left _ _)

/-- A closed rational interval `[lo, hi]`, the certified enclosure primitive. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi
  deriving Repr, DecidableEq

namespace Interval

/-- The set of reals an interval encloses. -/
def contains (x : Interval) (r : ℝ) : Prop :=
  (x.lo : ℝ) ≤ r ∧ r ≤ (x.hi : ℝ)

/-- The degenerate interval `[q, q]`. -/
def exact (q : ℚ) : Interval :=
  { lo := q, hi := q, le := le_refl q }

theorem contains_exact (q : ℚ) : (exact q).contains (q : ℝ) :=
  ⟨le_refl _, le_refl _⟩

def add (x y : Interval) : Interval :=
  { lo := x.lo + y.lo,
    hi := x.hi + y.hi,
    le := add_le_add x.le y.le }

theorem contains_add {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.add y).contains (a + b) := by
  refine ⟨?_, ?_⟩ <;> simp only [add] <;> push_cast
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

def neg (x : Interval) : Interval :=
  { lo := -x.hi,
    hi := -x.lo,
    le := neg_le_neg x.le }

theorem contains_neg {x : Interval} {a : ℝ}
    (hx : x.contains a) : x.neg.contains (-a) := by
  refine ⟨?_, ?_⟩ <;> simp only [neg] <;> push_cast
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

def sub (x y : Interval) : Interval :=
  x.add y.neg

theorem contains_sub {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.sub y).contains (a - b) :=
  sub_eq_add_neg a b ▸ contains_add hx (contains_neg hy)

/-- Interval product: the enclosure is the min/max of the four corner
products, which is sound in every sign configuration (`mul_corners_le`,
`le_mul_corners`). -/
def mul (x y : Interval) : Interval :=
  { lo := min (min (x.lo * y.lo) (x.lo * y.hi)) (min (x.hi * y.lo) (x.hi * y.hi)),
    hi := max (max (x.lo * y.lo) (x.lo * y.hi)) (max (x.hi * y.lo) (x.hi * y.hi)),
    le := le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _)) }

theorem contains_mul {x y : Interval} {a b : ℝ}
    (hx : x.contains a) (hy : y.contains b) : (x.mul y).contains (a * b) := by
  refine ⟨?_, ?_⟩ <;> simp only [mul] <;> push_cast
  · exact mul_corners_le hx.1 hx.2 hy.1 hy.2
  · exact le_mul_corners hx.1 hx.2 hy.1 hy.2

end Interval

/-- An axis-aligned rational rectangle in `ℂ`: certified enclosures for the
real and imaginary parts. -/
structure ComplexInterval where
  re : Interval
  im : Interval
  deriving Repr, DecidableEq

namespace ComplexInterval

/-- The set of complex numbers a rectangle encloses. -/
def contains (x : ComplexInterval) (z : ℂ) : Prop :=
  x.re.contains z.re ∧ x.im.contains z.im

/-- The degenerate rectangle `{q + r*I}`. -/
def exact (q r : ℚ) : ComplexInterval :=
  { re := Interval.exact q, im := Interval.exact r }

theorem contains_exact (q r : ℚ) :
    (exact q r).contains ⟨(q : ℝ), (r : ℝ)⟩ :=
  ⟨Interval.contains_exact q, Interval.contains_exact r⟩

theorem contains_zero : (exact 0 0).contains 0 := by
  constructor <;> simp [exact, Interval.contains, Interval.exact]

def add (x y : ComplexInterval) : ComplexInterval :=
  { re := x.re.add y.re, im := x.im.add y.im }

theorem contains_add {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.add y).contains (z + w) :=
  ⟨Interval.contains_add hx.1 hy.1, Interval.contains_add hx.2 hy.2⟩

def neg (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.neg, im := x.im.neg }

theorem contains_neg {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : x.neg.contains (-z) :=
  ⟨Interval.contains_neg hx.1, Interval.contains_neg hx.2⟩



/-- Complex product, routed through the real layer:
`(z*w).re = z.re*w.re − z.im*w.im` and `(z*w).im = z.re*w.im + z.im*w.re`. -/
def mul (x y : ComplexInterval) : ComplexInterval :=
  { re := (x.re.mul y.re).sub (x.im.mul y.im),
    im := (x.re.mul y.im).add (x.im.mul y.re) }

theorem contains_mul {x y : ComplexInterval} {z w : ℂ}
    (hx : x.contains z) (hy : y.contains w) : (x.mul y).contains (z * w) := by
  refine ⟨?_, ?_⟩
  · have h := Interval.contains_sub
      (Interval.contains_mul hx.1 hy.1) (Interval.contains_mul hx.2 hy.2)
    simpa [mul, Complex.mul_re] using h
  · have h := Interval.contains_add
      (Interval.contains_mul hx.1 hy.2) (Interval.contains_mul hx.2 hy.1)
    simpa [mul, Complex.mul_im] using h

end ComplexInterval

end ZetaLean


/- SOURCE: lean/ZetaLean/IntervalExp.lean -/





/-!
# Certified interval `exp` and `log`

The first stone of rung 3's numeric half.  `ZetaLean/DHZeroCriterion.lean`
reduced the Davenport-Heilbronn theorem to two interval inequalities about
`DH`; discharging them inside the kernel requires evaluating terms
`n^{-s} = exp(-s·log n)` with certified enclosures.  This file supplies the
real elementary functions that evaluation is made of, on the `Interval`
layer of `ZetaLean/Rigor.lean`:

* `Interval.exp1`, certified `exp` on intervals inside `[-1, 1]`: Taylor
  partial sums at the rational endpoints, inflated by the Lagrange remainder
  of Mathlib's `Real.exp_bound`, tightened by monotonicity (endpoints
  suffice; no interval Taylor needed).
* `Interval.expI`: `exp` on intervals inside `[-2^k, 2^k]`, by `k`
  halvings and certified squarings (`exp t = exp(t/2)²`).
* `Interval.log1`: certified `log` on intervals inside `(0, 2)`, from the
  alternating series bound `Real.abs_log_sub_add_sum_range_le`, again
  tightened by monotonicity.
* `Interval.log2I`: an enclosure of `log 2 = -log(1/2)`, the anchor for
  extending `log1` to all positive rationals by binary reduction
  (`log q = k·log 2 + log(q/2^k)`, future work).

Every operation returns an interval together with a containment theorem; the
smoke tests at the bottom (`exp_one_gt`, …) kernel-check concrete digits of
`e` and `log 2` end-to-end, which is the point: the same pipeline, pointed
at `DH`, is what will eventually discharge the two hypotheses of
`davenport_heilbronn_of_certified_disk`.
-/

namespace ZetaLean.Interval

open Finset

/-! ### Certified `exp` on `[-1, 1]` -/









/-! ### Range extension by halving and squaring -/

/-- Exact halving (tighter than routing through `mul`). -/
def halve (x : Interval) : Interval :=
  { lo := x.lo / 2, hi := x.hi / 2,
    le := by have := x.le; linarith }

theorem contains_halve {x : Interval} {t : ℝ} (hx : x.contains t) :
    x.halve.contains (t / 2) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩ <;> simp only [halve] <;> push_cast <;> linarith



/-! ### Certified `log` on `(0, 2)` -/

/-- Rational partial sum of the series for `-log(1-q)`. -/
def logSum (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, q ^ (i + 1) / (i + 1)

/-- Rational tail bound, matching `Real.abs_log_sub_add_sum_range_le`. -/
def logRem (n : ℕ) (q : ℚ) : ℚ :=
  |q| ^ (n + 1) / (1 - |q|)

private lemma logSum_cast (n : ℕ) (q : ℚ) :
    ((logSum n q : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ (i + 1) / (i + 1) := by
  unfold logSum
  push_cast
  rfl

private lemma logRem_cast (n : ℕ) (q : ℚ) :
    ((logRem n q : ℚ) : ℝ) = |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)|) := by
  unfold logRem
  push_cast
  rfl

/-- Series lower bound for `log (1 - q)` at a rational point. -/
theorem log_one_sub_lower {n : ℕ} {q : ℚ} (hq : |q| < 1) :
    ((-logSum n q - logRem n q : ℚ) : ℝ) ≤ Real.log (1 - q) := by
  have hq' : |(q : ℝ)| < 1 := by exact_mod_cast hq
  have h := Real.abs_log_sub_add_sum_range_le hq' n
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  push_cast
  rw [logSum_cast, logRem_cast]
  linarith

/-- Series upper bound for `log (1 - q)` at a rational point. -/
theorem log_one_sub_upper {n : ℕ} {q : ℚ} (hq : |q| < 1) :
    Real.log (1 - q) ≤ ((-logSum n q + logRem n q : ℚ) : ℝ) := by
  have hq' : |(q : ℝ)| < 1 := by exact_mod_cast hq
  have h := Real.abs_log_sub_add_sum_range_le hq' n
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  push_cast
  rw [logSum_cast, logRem_cast]
  linarith

/-- Certified `log` on an interval inside `(0, 2)`: the series for
`log(1-x)` at the endpoints `x = 1 - lo`, `x = 1 - hi`, plus monotonicity. -/
def log1 (n : ℕ) (x : Interval) : Interval :=
  { lo := -logSum n (1 - x.lo) - logRem n (1 - x.lo),
    hi := max (-logSum n (1 - x.hi) + logRem n (1 - x.hi))
      (-logSum n (1 - x.lo) - logRem n (1 - x.lo)),
    le := le_max_right _ _ }

theorem contains_log1 {n : ℕ} {x : Interval} {t : ℝ}
    (hx : x.contains t) (hlo : 0 < x.lo) (hhi : x.hi < 2) :
    (log1 n x).contains (Real.log t) := by
  have hlo2 : x.lo < 2 := lt_of_le_of_lt x.le hhi
  have hhi0 : 0 < x.hi := lt_of_lt_of_le hlo x.le
  have hq1 : |(1 - x.lo : ℚ)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hq2 : |(1 - x.hi : ℚ)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by exact_mod_cast hlo) hx.1
  have hxlo : (0 : ℝ) < (x.lo : ℝ) := by exact_mod_cast hlo
  have hxhi : (0 : ℝ) < (x.hi : ℝ) := by exact_mod_cast hhi0
  have hcast_lo : (1 : ℝ) - ((1 - x.lo : ℚ) : ℝ) = (x.lo : ℝ) := by push_cast; ring
  have hcast_hi : (1 : ℝ) - ((1 - x.hi : ℚ) : ℝ) = (x.hi : ℝ) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h1 := log_one_sub_lower (n := n) hq1
    rw [hcast_lo] at h1
    exact h1.trans ((Real.log_le_log_iff hxlo ht0).mpr hx.1)
  · have h2 := log_one_sub_upper (n := n) hq2
    rw [hcast_hi] at h2
    have h3 : Real.log t ≤ ((-logSum n (1 - x.hi) + logRem n (1 - x.hi) : ℚ) : ℝ) :=
      ((Real.log_le_log_iff ht0 hxhi).mpr hx.2).trans h2
    refine h3.trans ?_
    change _ ≤ (((log1 n x).hi : ℚ) : ℝ)
    rw [log1, Rat.cast_max]
    exact le_max_left _ _

/-- An enclosure of `log 2 = -log(1/2)`. -/
def log2I (n : ℕ) : Interval :=
  (log1 n (Interval.exact (1 / 2))).neg

theorem contains_log2I (n : ℕ) : (log2I n).contains (Real.log 2) := by
  have h := contains_log1 (n := n) (Interval.contains_exact (1 / 2))
    (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  have h2 := Interval.contains_neg h
  rw [show -Real.log ((1 / 2 : ℚ) : ℝ) = Real.log 2 by
    rw [← Real.log_inv]; norm_num] at h2
  exact h2

/-! ### `log` of any positive rational -/

/-- Certified `log q` for a positive rational, by the binary reduction the
module docstring promised: `log q = k·log 2 + log (q / 2^k)`, with the second
summand landed in the domain of `log1`.  The caller picks `k`;
`contains_logQ` demands exactly the side conditions that make the choice
correct, and both are `norm_num`-decidable at any concrete call site. -/
def logQ (n k : ℕ) (q : ℚ) : Interval :=
  ((Interval.exact (k : ℚ)).mul (log2I n)).add (log1 n (Interval.exact (q / 2 ^ k)))

theorem contains_logQ {n k : ℕ} {q : ℚ} (h0 : 0 < q / 2 ^ k) (h2 : q / 2 ^ k < 2) :
    (logQ n k q).contains (Real.log q) := by
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  have hq0 : (0 : ℚ) < q := by
    have := mul_pos h0 h2k
    rwa [div_mul_cancel₀ _ h2k.ne'] at this
  have hid : Real.log q = (k : ℝ) * Real.log 2 + Real.log ((q : ℝ) / 2 ^ k) := by
    rw [Real.log_div (by exact_mod_cast hq0.ne') (by positivity), Real.log_pow]
    ring
  have hA := Interval.contains_mul (Interval.contains_exact (k : ℚ)) (contains_log2I n)
  have hB := contains_log1 (n := n) (Interval.contains_exact (q / 2 ^ k)) h0 h2
  have hC := Interval.contains_add hA hB
  have hcast : ((q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by push_cast; ring
  rw [hcast] at hC
  rw [hid, show ((k : ℝ)) = (((k : ℚ) : ℝ)) by push_cast; rfl]
  exact hC

/-! ### Smoke tests: kernel-checked digits of `e` and `log 2`

These are the end-to-end proof that the pipeline computes: the same
machinery, pointed at `DH`'s Dirichlet terms, is what will discharge the
hypotheses of `davenport_heilbronn_of_certified_disk`. -/








end ZetaLean.Interval


/- SOURCE: lean/ZetaLean/IntervalCExp.lean -/
/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/






/-!
# Certified complex `exp`, and the Dirichlet term `n^{-s}`

The second and third stones of rung 3's numeric half.  `IntervalExp.lean`
certified the real elementary functions; this file lifts `exp` to `ℂ` on the
`ComplexInterval` layer of `ZetaLean/Rigor.lean` and then ties the Dirichlet
term `n^{-s} = exp(-s · log n)` to a kernel-checked enclosure, the gap
`ZetaLean/OracleDH.lean` names as "nothing here is kernel-checked about
`n^{-s}` itself".

* `ComplexInterval.expSumC`: the Taylor partial sum `∑_{i<n} z^i/i!` as
  rectangle arithmetic, sound by induction from `Rigor.lean`.
* `ComplexInterval.expSmall`, `exp` on a box with `normBound ≤ 1`: the
  Taylor sum inflated by the Lagrange-style remainder of Mathlib's
  `Complex.exp_bound`.  Since `exp(it)` has real part `cos t` and imaginary
  part `sin t`, this is simultaneously certified sin/cos, no separate
  trigonometric development is needed.
* `ComplexInterval.expC`: `exp` on a box with `normBound ≤ 2^k`, by `k`
  halvings and certified squarings (`exp z = exp(z/2)²`), mirroring
  `Interval.expI`.
* `ComplexInterval.dirichletTerm`: the enclosure of `m^{-s}` for natural
  `m ≥ 1` and rational `s`, composed from `Interval.logQ` and `expC` through
  Mathlib's `cpow_def_of_ne_zero` bridge.  `contains_dirichletTerm` is the
  theorem the oracle could not fake: the box is computed by kernel-reducible
  rational arithmetic and provably contains `(m : ℂ) ^ (-s)`.

What remains open of rung 3 Phase B after this file: the tail bound for the
analytic continuation (the series does not converge absolutely at
`Re s ≈ 0.808`; see the note at the bottom of `OracleDH.lean`), and the
assembly of the two disk inequalities of
`davenport_heilbronn_of_certified_disk` from term enclosures.

The smoke tests kernel-check digits of `cos 1`, `sin 1` and `cos 2`
end-to-end through the complex pipeline.
-/

namespace ZetaLean

/-- `|t| ≤ max |lo| |hi|` for `t ∈ [lo, hi]`: the endpoint bound that turns
interval containment into a norm bound. -/
private theorem abs_le_max_abs_endpoints {lo t hi : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) :
    |t| ≤ max |lo| |hi| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -(max |lo| |hi|) ≤ -|lo| := neg_le_neg (le_max_left _ _)
      _ ≤ lo := neg_abs_le lo
      _ ≤ t := h1
  · calc t ≤ hi := h2
      _ ≤ |hi| := le_abs_self hi
      _ ≤ max |lo| |hi| := le_max_right _ _

namespace ComplexInterval

open Finset

/-! ### Powers, rational scaling, Taylor partial sums -/

/-- Interval power by iterated corner multiplication. -/
def powI (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => exact 1 0
  | m + 1 => (powI x m).mul x

theorem contains_powI {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ∀ m, (powI x m).contains (z ^ m)
  | 0 => by
    rw [pow_zero]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [powI, exact, Interval.exact, Interval.contains]
  | m + 1 => by
    rw [pow_succ]
    exact contains_mul (contains_powI hx m) hx

/-- Scale a box by a rational scalar (viewed in `ℂ` through `ℝ`). -/
def smulQ (q : ℚ) (x : ComplexInterval) : ComplexInterval :=
  (exact q 0).mul x

theorem contains_smulQ {q : ℚ} {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    (smulQ q x).contains ((((q : ℚ) : ℝ) : ℂ) * z) := by
  have hq : (exact q 0).contains (((q : ℝ) : ℂ)) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [exact, Interval.exact, Interval.contains]
  exact contains_mul hq hx

/-- The Taylor partial sum `∑_{i<m} z^i / i!` as rectangle arithmetic. -/
def expSumC (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => exact 0 0
  | m + 1 => (expSumC x m).add (smulQ (1 / m.factorial) (powI x m))

theorem contains_expSumC {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ∀ m, (expSumC x m).contains (∑ i ∈ range m, z ^ i / i.factorial)
  | 0 => by simpa [expSumC] using contains_zero
  | m + 1 => by
    rw [Finset.sum_range_succ]
    have h := contains_smulQ (q := 1 / m.factorial) (contains_powI hx m)
    rw [show ((((1 / m.factorial : ℚ) : ℝ)) : ℂ) * z ^ m = z ^ m / m.factorial by
      push_cast; ring] at h
    exact contains_add (contains_expSumC hx m) h

/-! ### Norm bound and remainder inflation -/

/-- A rational bound on `‖z‖` valid for every `z` in the box: endpoint bounds
per component, combined by the triangle inequality `‖z‖ ≤ |re z| + |im z|`. -/
def normBound (x : ComplexInterval) : ℚ :=
  max |x.re.lo| |x.re.hi| + max |x.im.lo| |x.im.hi|

theorem norm_le_normBound {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    ‖z‖ ≤ (normBound x : ℝ) := by
  have hre : |z.re| ≤ ((max |x.re.lo| |x.re.hi| : ℚ) : ℝ) := by
    push_cast
    exact abs_le_max_abs_endpoints hx.1.1 hx.1.2
  have him : |z.im| ≤ ((max |x.im.lo| |x.im.hi| : ℚ) : ℝ) := by
    push_cast
    exact abs_le_max_abs_endpoints hx.2.1 hx.2.2
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add hre him
    _ = ((normBound x : ℚ) : ℝ) := by rw [normBound]; push_cast; ring

/-- Widen a box by `|r|` in every direction. -/
def inflate (x : ComplexInterval) (r : ℚ) : ComplexInterval :=
  { re := { lo := x.re.lo - |r|, hi := x.re.hi + |r|,
            le := by have h1 := x.re.le; have h2 := abs_nonneg r; linarith },
    im := { lo := x.im.lo - |r|, hi := x.im.hi + |r|,
            le := by have h1 := x.im.le; have h2 := abs_nonneg r; linarith } }

/-- Soundness of `inflate`: if the box contains `z` and `‖w - z‖ ≤ r`, the
inflated box contains `w`. -/
theorem contains_inflate {x : ComplexInterval} {z w : ℂ} {r : ℚ}
    (hx : x.contains z) (hw : ‖w - z‖ ≤ (r : ℝ)) : (x.inflate r).contains w := by
  have hre : |w.re - z.re| ≤ |(r : ℝ)| :=
    calc |w.re - z.re| = |(w - z).re| := by rw [Complex.sub_re]
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
      _ ≤ (r : ℝ) := hw
      _ ≤ |(r : ℝ)| := le_abs_self _
  have him : |w.im - z.im| ≤ |(r : ℝ)| :=
    calc |w.im - z.im| = |(w - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      _ ≤ (r : ℝ) := hw
      _ ≤ |(r : ℝ)| := le_abs_self _
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  obtain ⟨him1, him2⟩ := abs_le.mp him
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [inflate] <;> push_cast <;> linarith

/-! ### `exp` on a small box, then on any box by halving and squaring -/

/-- Certified `exp` on a box with `normBound ≤ 1`: Taylor sum plus the
remainder of `Complex.exp_bound`, which is monotone in `‖z‖` and therefore
bounded by the same expression in `normBound`. -/
def expSmall (n : ℕ) (x : ComplexInterval) : ComplexInterval :=
  (expSumC x n).inflate (normBound x ^ n * ((n + 1) / (n.factorial * n)))

theorem contains_expSmall {n : ℕ} (hn : 0 < n) {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) (hb : normBound x ≤ 1) :
    (expSmall n x).contains (Complex.exp z) := by
  have hzb : ‖z‖ ≤ (normBound x : ℝ) := norm_le_normBound hx
  have hz1 : ‖z‖ ≤ 1 := hzb.trans (by exact_mod_cast hb)
  have h := Complex.exp_bound hz1 hn
  refine contains_inflate (contains_expSumC hx n) (h.trans ?_)
  have h1 : ‖z‖ ^ n ≤ (normBound x : ℝ) ^ n :=
    pow_le_pow_left₀ (norm_nonneg z) hzb n
  have h2 : (0 : ℝ) ≤ (n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹ := by positivity
  calc ‖z‖ ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹)
      ≤ (normBound x : ℝ) ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ((normBound x ^ n * ((n + 1) / (n.factorial * n)) : ℚ) : ℝ) := by
        push_cast [Nat.succ_eq_add_one]
        ring

/-- Componentwise exact halving. -/
def halveC (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.halve, im := x.im.halve }

theorem contains_halveC {x : ComplexInterval} {z : ℂ} (hx : x.contains z) :
    (halveC x).contains (z / 2) := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  constructor
  · rw [show (z / 2).re = z.re / 2 by rw [h2, Complex.div_ofReal_re]]
    exact Interval.contains_halve hx.1
  · rw [show (z / 2).im = z.im / 2 by rw [h2, Complex.div_ofReal_im]]
    exact Interval.contains_halve hx.2

theorem normBound_halveC (x : ComplexInterval) :
    normBound (halveC x) = normBound x / 2 := by
  simp only [normBound, halveC, Interval.halve, abs_div, abs_two]
  rw [max_div_div_right (by norm_num : (0 : ℚ) ≤ 2),
    max_div_div_right (by norm_num : (0 : ℚ) ≤ 2)]
  ring



/-! ### The Dirichlet term `m^{-s}` -/



/-! ### Outward rounding

Exact rational interval arithmetic doubles digit counts at every squaring:
one Dirichlet term at the oracle point, evaluated without rounding, has
560000-bit endpoints.  `coarsen` is the primitive Arb has and the exact
layer lacked: round the endpoints outward to `p` dyadic bits.  Containment
is preserved, the box only grows, by at most `2^{-p}` per side. -/

/-- Round an interval's endpoints outward to `p` dyadic bits. -/
def _root_.ZetaLean.Interval.coarsen (p : ℕ) (x : Interval) : Interval :=
  { lo := (⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p,
    hi := (⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p,
    le := by
      have h2 : (0 : ℚ) < 2 ^ p := by positivity
      rw [div_le_div_iff_of_pos_right h2]
      calc ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℚ) ≤ x.lo * 2 ^ p := Int.floor_le _
        _ ≤ x.hi * 2 ^ p := by nlinarith [x.le]
        _ ≤ ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℚ) := Int.le_ceil _ }

theorem _root_.ZetaLean.Interval.contains_coarsen (p : ℕ) {x : Interval} {t : ℝ}
    (hx : x.contains t) : (x.coarsen p).contains t := by
  obtain ⟨h1, h2⟩ := hx
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  constructor
  · show (((⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p : ℚ) : ℝ) ≤ t
    rw [show (((⌊x.lo * 2 ^ p⌋ : ℤ) / 2 ^ p : ℚ) : ℝ)
        = ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℝ) / 2 ^ p by push_cast; ring,
      div_le_iff₀ h2p]
    calc ((⌊x.lo * 2 ^ p⌋ : ℤ) : ℝ) ≤ ((x.lo * 2 ^ p : ℚ) : ℝ) := by
          exact_mod_cast Int.floor_le _
      _ = (x.lo : ℝ) * 2 ^ p := by push_cast; ring
      _ ≤ t * 2 ^ p := by nlinarith
  · show t ≤ (((⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p : ℚ) : ℝ)
    rw [show (((⌈x.hi * 2 ^ p⌉ : ℤ) / 2 ^ p : ℚ) : ℝ)
        = ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℝ) / 2 ^ p by push_cast; ring,
      le_div_iff₀ h2p]
    calc t * 2 ^ p ≤ (x.hi : ℝ) * 2 ^ p := by nlinarith
      _ = ((x.hi * 2 ^ p : ℚ) : ℝ) := by push_cast; ring
      _ ≤ ((⌈x.hi * 2 ^ p⌉ : ℤ) : ℝ) := by exact_mod_cast Int.le_ceil _

/-- Componentwise outward rounding of a rectangle. -/
def coarsen (p : ℕ) (x : ComplexInterval) : ComplexInterval :=
  { re := x.re.coarsen p, im := x.im.coarsen p }

theorem contains_coarsen (p : ℕ) {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : (x.coarsen p).contains z :=
  ⟨Interval.contains_coarsen p hx.1, Interval.contains_coarsen p hx.2⟩

/-- `expC` with outward rounding to `p` bits after every squaring, the
digit-growth-free evaluator.  Identical enclosure semantics, boxes wider by
at most `2^{-p}` per level. -/
def expCr (n p : ℕ) : ℕ → ComplexInterval → ComplexInterval
  | 0, x => (expSmall n x).coarsen p
  | k + 1, x =>
    let y := expCr n p k (halveC x)
    (y.mul y).coarsen p

theorem contains_expCr (n p : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ), x.contains z →
      normBound x ≤ 2 ^ k → (expCr n p k x).contains (Complex.exp z)
  | 0, x, z, hx, hb =>
    contains_coarsen p (contains_expSmall hn hx (by simpa using hb))
  | k + 1, x, z, hx, hb => by
    have hy : (expCr n p k (halveC x)).contains (Complex.exp (z / 2)) := by
      refine contains_expCr n p hn k (halveC x) (z / 2) (contains_halveC hx) ?_
      rw [normBound_halveC]
      rw [pow_succ] at hb
      linarith
    have h := contains_mul hy hy
    rw [show Complex.exp (z / 2) * Complex.exp (z / 2) = Complex.exp z by
      rw [← Complex.exp_add]; ring_nf] at h
    exact contains_coarsen p h

/-! ### The boxed-`s` Dirichlet term

The square-contour boundary segments range over sets of `s`, so the
enclosure must accept a rectangle for `s`, not only an exact point.  Same
pipeline; only the `-s` factor changes from an exact rectangle to `S.neg`. -/



/-! ### Separating the two Taylor orders

`dirichletTermBox` uses one order `n` for both series it runs: the logarithm
`Interval.logQ n kL m` and the exponential `expCr n p kE`.  Measured on plan v2's
worst grid site, that coupling is what makes the plan infeasible, and the two
orders want opposite things:

* The **width** is set almost entirely by the log.  `logRem n q ≈ q^{n+1}/(1-q)`
  with `q ≤ 1/2`, so at `n = 20` the log carries width `7.6e-6`, which `|s| ≈ 86`
  amplifies to `6.6e-4` and the squaring tower to `3.0e-3`.  Multiplied over the
  `5K` terms of one site that is a box width of `1.5` against a `β` of `0.038`,
  infeasible by a factor of 30, before any Lean is generated.  Raising `kE` or
  the coarsening precision does not touch it: at `kE = 18` and `p = 128` the
  final width is still `3.0e-3`.  Raising the log order does: `n = 28` gives
  `3.0e-8` and `n = 32` gives `1.9e-9`.
* The **literal size** is set almost entirely by the exponential.  `expSmall`
  forms `powI x i` up to `i = n`, so `n` multiplies the endpoint bit-width by
  `n`; that is where the "multi-thousand-bit rationals" that defeated one-shot
  `norm_num` evaluation come from.  The log's own endpoints are small and stay
  small, order 20 to 32 takes them from 91 to 158 bits.

So the orders are split.  `nLog` is raised until the width fits; `nExp` stays
small so the generated literals stay evaluable.  Nothing else changes: the two
series are independent and the containment proof is the same argument. -/

/-- `dirichletTermBox` with the logarithm's Taylor order separated from the
exponential's.  `dirichletTermBox n p kL kE m S` is the `nLog = nExp = n` case. -/
def dirichletTermBox2 (nLog nExp p kL kE : ℕ) (m : ℕ) (S : ComplexInterval) :
    ComplexInterval :=
  expCr nExp p kE (S.neg.mul { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 })

theorem contains_dirichletTermBox2 {nLog nExp p kL kE : ℕ} (hnL : 0 < nLog)
    (hnE : 0 < nExp) {m : ℕ} (hm : 0 < m) {S : ComplexInterval} {s : ℂ}
    (hS : S.contains s) (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound (S.neg.mul
      { re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (dirichletTermBox2 nLog nExp p kL kE m S).contains ((m : ℂ) ^ (-s)) := by
  have hlogQ := Interval.contains_logQ (n := nLog) (k := kL) (q := (m : ℚ)) h0 h2
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlogQ
  have hL : ({ re := Interval.logQ nLog kL (m : ℚ), im := Interval.exact 0 } :
      ComplexInterval).contains ((Real.log m : ℝ) : ℂ) := by
    constructor
    · rw [Complex.ofReal_re]; exact hlogQ
    · rw [Complex.ofReal_im]; norm_num [Interval.contains, Interval.exact]
  have hexp := contains_expCr nExp p hnE kE _ _ (contains_mul (contains_neg hS) hL) hb
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show ((m : ℂ) ^ (-s)) = Complex.exp (-s * ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hm0,
      show Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    , mul_comm]]
  exact hexp


/-! ### Reading a norm lower bound off a computed box -/





end ComplexInterval

end ZetaLean


/- SOURCE: hunts/hardy_first_zero/lean/HardyFirstZero/BoxSupport.lean -/





/-!
# Support for the two term-box tables (hunt `hardy_first_zero`)

Generic pieces between `EulerMaclaurin.lean` (the remainder) and the generated
`Boxes.lean` (the term boxes at the two endpoints):

* `lit`, `sumBoxes`, `contains_sumBoxes`: literal rectangles and their running sum;
* `ptBox`, `ptBox_contains`: the exact rectangle of `1/2 + it`;
* `main_eq`: the order-4 main term as `Σ_{i<N} i^{-s} + N^{-s} · c_N(s)` with
  `c_N(s) = N/(s-1) + 1/2 + s/(12N)`, so that it needs `N` term boxes and one
  exact product;
* `em30_bound`: the remainder at `N = 30` on the critical line, bounded by an
  explicit rational function of the height.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval
open scoped ComplexConjugate

namespace HardyFirstZero

/-- A literal rectangle. -/
def lit (a b c d : ℚ) (h1 : a ≤ b) (h2 : c ≤ d) : ComplexInterval := ⟨⟨a, b, h1⟩, ⟨c, d, h2⟩⟩

/-- The running sum `B 0 + ⋯ + B (n-1)` of rectangles. -/
def sumBoxes (B : ℕ → ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | n + 1 => (sumBoxes B n).add (B n)

theorem contains_sumBoxes {B : ℕ → ComplexInterval} {f : ℕ → ℂ} :
    ∀ {N : ℕ}, (∀ m < N, (B m).contains (f m)) →
      (sumBoxes B N).contains (∑ m ∈ range N, f m)
  | 0, _ => by simpa [sumBoxes] using contains_zero
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    exact contains_add (contains_sumBoxes fun m hm => h m (by omega)) (h n (by omega))

/-- The exact rectangle of `1/2 + it`. -/
def ptBox (t : ℚ) : ComplexInterval := ComplexInterval.exact (1 / 2) t

theorem ptBox_contains (t : ℚ) : (ptBox t).contains (sOf (t : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp [ptBox, ComplexInterval.exact, Interval.exact, sOf]

/-- The order-4 main term, regrouped around the single power `N^{-s}`. -/
theorem main_eq (s : ℂ) {N : ℕ} (hN : N ≠ 0) :
    ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
      = ∑ i ∈ range N, (i : ℂ) ^ (-s)
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2 + s / (12 * N)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h1 : (N : ℂ) ^ (1 - s) = N * (N : ℂ) ^ (-s) := by
    rw [show (1 - s) = 1 + (-s) by ring, cpow_add _ _ hN', cpow_one]
  have h2 : (N : ℂ) ^ (-s - 1) = (N : ℂ) ^ (-s) * (N : ℂ)⁻¹ := by
    rw [show (-s - 1) = -s + (-1) by ring, cpow_add _ _ hN', cpow_neg_one]
  rw [h1, h2]
  ring

/-- `‖z + j‖ ≤ (1/2 + j) + t` on the critical line. -/
private lemma norm_add_le_of_sOf {t : ℝ} (ht : 0 ≤ t) (j : ℝ) (hj : 0 ≤ j) :
    ‖sOf t + j‖ ≤ 1 / 2 + j + t := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  have hre : (sOf t + j).re = 1 / 2 + j := by simp [sOf]
  have him : (sOf t + j).im = t := by simp [sOf]
  rw [hre, him, abs_of_nonneg (by linarith), abs_of_nonneg ht]

/-- **The remainder at `N = 30` on the critical line**, for `0 < t ≤ T`:
`‖ζ(1/2+it) - M_30‖ ≤ (1/2+T)(3/2+T)(5/2+T)(7/2+T) / (24389 · 5 · (7/2) · 720)`,
from `zeta_em4_error`, `‖z‖ ≤ |Re z| + |Im z|` and `29^{-7/2} ≤ 1/(29³ · 5)`. -/
theorem em30_bound {t T : ℝ} (ht : 0 < t) (hT : t ≤ T) :
    ‖riemannZeta (sOf t) - (∑ i ∈ range 30, (i : ℂ) ^ (-sOf t) + ((30 : ℕ) : ℂ) ^ (1 - sOf t)
        / (sOf t - 1) + ((30 : ℕ) : ℂ) ^ (-sOf t) / 2
        + sOf t / 12 * ((30 : ℕ) : ℂ) ^ (-sOf t - 1))‖
      ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) / (24389 * 5 * (7 / 2) * 720) := by
  have hQP : sOf t ∈ QP := ⟨by simp [sOf], by simp [sOf, ht]⟩
  have h := zeta_em4_error hQP (N := 30) (by norm_num)
  refine h.trans ?_
  have hre : (sOf t).re = 1 / 2 := sOf_re t
  rw [hre]
  -- the four norms
  have e0 : ‖sOf t‖ ≤ 1 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 0 le_rfl; simp at this; linarith
  have e1 : ‖sOf t + 1‖ ≤ 3 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 1 zero_le_one; push_cast at this; linarith
  have e2 : ‖sOf t + 2‖ ≤ 5 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 2 zero_le_two; push_cast at this; linarith
  have e3 : ‖sOf t + 3‖ ≤ 7 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 3 (by norm_num); push_cast at this; linarith
  have hT0 : 0 ≤ T := by linarith
  have hP : ‖P4 (sOf t)‖ ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) := by
    unfold P4
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul e0 e1 (norm_nonneg _) (by linarith)
    have a2 := mul_le_mul a1 e2 (norm_nonneg _) (mul_nonneg (by linarith) (by linarith))
    exact mul_le_mul a2 e3 (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  -- the power of 29
  have h29 : ((30 : ℕ) : ℝ) - 1 = 29 := by norm_num
  rw [h29]
  have hpow : (29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) ≤ 1 / (24389 * 5) := by
    rw [show (-(1 / 2 : ℝ) - 3) = -(1 / 2) + (-3 : ℝ) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hs : (5 : ℝ) ≤ Real.sqrt 29 := Real.le_sqrt_of_sq_le (by norm_num)
    have hs0 : 0 < Real.sqrt 29 := by positivity
    rw [show (1 : ℝ) / (24389 * 5) = (5 : ℝ)⁻¹ * ((29 : ℝ) ^ 3)⁻¹ by norm_num]
    gcongr
  have hnn : 0 ≤ (29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) := Real.rpow_nonneg (by norm_num) _
  have hQ0 : 0 ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  calc ‖P4 (sOf t)‖ * ((29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) / (1 / 2 + 3)) / 720
      ≤ ((1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T))
          * ((1 / (24389 * 5)) / (1 / 2 + 3)) / 720 :=
        div_le_div_of_nonneg_right (mul_le_mul hP
          (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity) hQ0) (by norm_num)
    _ = _ := by ring

end HardyFirstZero
end

section
open Complex
open scoped ComplexConjugate

namespace HardyFirstZero

/-- Apply the phase estimate from bueno_ricardo's first-zero certificate to the
    interval (21.016, 21.029). Its width gives a phase bound of 3/2 radians. -/
theorem gammaR_re_pos_second :
    0 < (Gammaℝ (sOf (2627 / 125)) * conj (Gammaℝ (sOf (21029 / 1000)))).re := by
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogpi' := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi4 := Real.pi_le_four
  refine gammaR_re_pos (L := 3 / 2) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) ?_ ?_
  · unfold dl
    linarith
  · unfold dl
    linarith

end HardyFirstZero
end

section
/- Prime terms use the exact rational exponential. Composite terms follow from
   the multiplicativity of n^(-s), as in Thomas Lince's zeta-lab hunt #133. -/
open Complex ZetaLean ZetaLean.ComplexInterval HardyFirstZero
namespace HardySecondInterval
set_option maxRecDepth 100000
theorem contains_cpow_mul_coarsen (p : ℕ) {a b : ℕ} {A B : ComplexInterval} {s : ℂ}
    (hA : A.contains ((a : ℂ) ^ (-s))) (hB : B.contains ((b : ℂ) ^ (-s))) :
    ((A.mul B).coarsen p).contains (((a * b : ℕ) : ℂ) ^ (-s)) := by
  have h := contains_mul hA hB
  rw [show (((a * b : ℕ) : ℂ) ^ (-s)) = ((a : ℂ) ^ (-s)) * ((b : ℂ) ^ (-s)) by
    rw [Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow a b (-s)]
  exact contains_coarsen p h

/-- The first term, `1^{-s} = 1`, exactly. -/
theorem contains_one_cpow (s : ℂ) :
    (ComplexInterval.exact 1 0).contains (((1 : ℕ) : ℂ) ^ (-s)) := by
  have h := contains_exact 1 0
  rw [Nat.cast_one, Complex.one_cpow]
  convert h using 1
  apply Complex.ext <;> simp


def tA : ℕ → ComplexInterval
  | 1 => ComplexInterval.exact 1 0
  | 2 => lit (-633058925 / 2147483648 : ℚ) (-316508599 / 1073741824 : ℚ) (-2760553077 / 4294967296 : ℚ) (-690117429 / 1073741824 : ℚ) (by decide +kernel) (by decide +kernel)
  | 3 => lit (-565399709 / 2147483648 : ℚ) (-282687033 / 1073741824 : ℚ) (1103421141 / 2147483648 : ℚ) (2206893601 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 4 => lit (-1401130623 / 4294967296 : ℚ) (-1400974263 / 4294967296 : ℚ) (203427021 / 536870912 : ℚ) (101723287 / 268435456 : ℚ) (by decide +kernel) (by decide +kernel)
  | 5 => lit (-1426770133 / 4294967296 : ℚ) (-713336777 / 2147483648 : ℚ) (-1286055239 / 4294967296 : ℚ) (-1285958681 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 6 => lit (875849197 / 2147483648 : ℚ) (875905651 / 2147483648 : ℚ) (76184187 / 4294967296 : ℚ) (76297107 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 7 => lit (-810486049 / 2147483648 : ℚ) (-1620890209 / 4294967296 : ℚ) (44227997 / 2147483648 : ℚ) (88537885 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 8 => lit (1458943507 / 4294967296 : ℚ) (729574475 / 2147483648 : ℚ) (210321545 / 2147483648 : ℚ) (420848515 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 9 => lit (-836278319 / 4294967296 : ℚ) (-836198575 / 4294967296 : ℚ) (-145260361 / 536870912 : ℚ) (-1162003161 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 10 => lit (-203029015 / 2147483648 : ℚ) (-6342419 / 67108864 : ℚ) (1296018497 / 4294967296 : ℚ) (1296161715 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 11 => lit (1284251805 / 4294967296 : ℚ) (1284297363 / 4294967296 : ℚ) (-41551025 / 1073741824 : ℚ) (-166158533 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 12 => lit (-467453017 / 4294967296 : ℚ) (-233655819 / 2147483648 : ℚ) (-71778329 / 268435456 : ℚ) (-574155963 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 13 => lit (-130831721 / 536870912 : ℚ) (-1046513837 / 4294967296 : ℚ) (568826813 / 4294967296 : ℚ) (284483377 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 14 => lit (534645013 / 4294967296 : ℚ) (534755001 / 4294967296 : ℚ) (507840763 / 2147483648 : ℚ) (126973935 / 536870912 : ℚ) (by decide +kernel) (by decide +kernel)
  | 15 => lit (1036356307 / 4294967296 : ℚ) (1036463751 / 4294967296 : ℚ) (-197281421 / 2147483648 : ℚ) (-394455391 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 16 => lit (-159787485 / 4294967296 : ℚ) (-79779187 / 2147483648 : ℚ) (-1061917735 / 4294967296 : ℚ) (-16588885 / 67108864 : ℚ) (by decide +kernel) (by decide +kernel)
  | 17 => lit (-1030487275 / 4294967296 : ℚ) (-1030270533 / 4294967296 : ℚ) (-153153349 / 4294967296 : ℚ) (-152936611 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 18 => lit (-250215565 / 2147483648 : ℚ) (-62539697 / 536870912 : ℚ) (879968705 / 4294967296 : ℚ) (27502571 / 134217728 : ℚ) (by decide +kernel) (by decide +kernel)
  | 19 => lit (285905941 / 2147483648 : ℚ) (71504615 / 536870912 : ℚ) (401124701 / 2147483648 : ℚ) (802474431 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 20 => lit (238157921 / 1073741824 : ℚ) (952798997 / 4294967296 : ℚ) (-60603247 / 2147483648 : ℚ) (-121039163 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 21 => lit (381242689 / 4294967296 : ℚ) (95331685 / 1073741824 : ℚ) (-856218753 / 4294967296 : ℚ) (-428067345 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 22 => lit (-121356399 / 1073741824 : ℚ) (-242677349 / 2147483648 : ℚ) (-194123051 / 1073741824 : ℚ) (-388210667 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 23 => lit (-55811855 / 268435456 : ℚ) (-892703557 / 4294967296 : ℚ) (-545663 / 33554432 : ℚ) (-69558743 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 24 => lit (-600408201 / 4294967296 : ℚ) (-600244311 / 4294967296 : ℚ) (319420595 / 2147483648 : ℚ) (639005109 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 25 => lit (44407713 / 2147483648 : ℚ) (44468707 / 2147483648 : ℚ) (854322333 / 4294967296 : ℚ) (26701385 / 134217728 : ℚ) (by decide +kernel) (by decide +kernel)
  | 26 => lit (337040017 / 2147483648 : ℚ) (337121303 / 2147483648 : ℚ) (252445553 / 2147483648 : ℚ) (15782927 / 134217728 : ℚ) (by decide +kernel) (by decide +kernel)
  | 27 => lit (12768897 / 67108864 : ℚ) (102161905 / 536870912 : ℚ) (-123783101 / 4294967296 : ℚ) (-123697267 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 28 => lit (495159821 / 4294967296 : ℚ) (123823255 / 1073741824 : ℚ) (-160788843 / 1073741824 : ℚ) (-80377769 / 536870912 : ℚ) (by decide +kernel) (by decide +kernel)
  | 29 => lit (-64936965 / 4294967296 : ℚ) (-16127143 / 1073741824 : ℚ) (-795139839 / 4294967296 : ℚ) (-794711447 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 30 => lit (-559142075 / 4294967296 : ℚ) (-69876693 / 536870912 : ℚ) (-549903863 / 4294967296 : ℚ) (-137443837 / 1073741824 : ℚ) (by decide +kernel) (by decide +kernel)
  | _ => ComplexInterval.exact 0 0

theorem tA_mem_1 :
    (tA 1).contains (((1 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := contains_one_cpow _

theorem tA_eq_2 : dirichletTermBox2 24 5 32 2 10 2 (ptBox (2627 / 125 : ℚ)) = tA 2 := by decide +kernel
theorem tA_mem_2 :
    (tA 2).contains (((2 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_2]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_3 : dirichletTermBox2 24 5 32 2 10 3 (ptBox (2627 / 125 : ℚ)) = tA 3 := by decide +kernel
theorem tA_mem_3 :
    (tA 3).contains (((3 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_3]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_4 : ((tA 2).mul (tA 2)).coarsen 32 = tA 4 := by decide +kernel
theorem tA_mem_4 :
    (tA 4).contains (((4 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_4]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_2

theorem tA_eq_5 : dirichletTermBox2 24 5 32 3 10 5 (ptBox (2627 / 125 : ℚ)) = tA 5 := by decide +kernel
theorem tA_mem_5 :
    (tA 5).contains (((5 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_5]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_6 : ((tA 2).mul (tA 3)).coarsen 32 = tA 6 := by decide +kernel
theorem tA_mem_6 :
    (tA 6).contains (((6 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_6]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_3

theorem tA_eq_7 : dirichletTermBox2 24 5 32 3 10 7 (ptBox (2627 / 125 : ℚ)) = tA 7 := by decide +kernel
theorem tA_mem_7 :
    (tA 7).contains (((7 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_7]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_8 : ((tA 2).mul (tA 4)).coarsen 32 = tA 8 := by decide +kernel
theorem tA_mem_8 :
    (tA 8).contains (((8 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_8]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_4

theorem tA_eq_9 : ((tA 3).mul (tA 3)).coarsen 32 = tA 9 := by decide +kernel
theorem tA_mem_9 :
    (tA 9).contains (((9 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_9]
  exact contains_cpow_mul_coarsen 32 tA_mem_3 tA_mem_3

theorem tA_eq_10 : ((tA 2).mul (tA 5)).coarsen 32 = tA 10 := by decide +kernel
theorem tA_mem_10 :
    (tA 10).contains (((10 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_10]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_5

theorem tA_eq_11 : dirichletTermBox2 24 5 32 4 10 11 (ptBox (2627 / 125 : ℚ)) = tA 11 := by decide +kernel
theorem tA_mem_11 :
    (tA 11).contains (((11 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_11]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_12 : ((tA 2).mul (tA 6)).coarsen 32 = tA 12 := by decide +kernel
theorem tA_mem_12 :
    (tA 12).contains (((12 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_12]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_6

theorem tA_eq_13 : dirichletTermBox2 24 5 32 4 10 13 (ptBox (2627 / 125 : ℚ)) = tA 13 := by decide +kernel
theorem tA_mem_13 :
    (tA 13).contains (((13 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_13]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_14 : ((tA 2).mul (tA 7)).coarsen 32 = tA 14 := by decide +kernel
theorem tA_mem_14 :
    (tA 14).contains (((14 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_14]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_7

theorem tA_eq_15 : ((tA 3).mul (tA 5)).coarsen 32 = tA 15 := by decide +kernel
theorem tA_mem_15 :
    (tA 15).contains (((15 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_15]
  exact contains_cpow_mul_coarsen 32 tA_mem_3 tA_mem_5

theorem tA_eq_16 : ((tA 2).mul (tA 8)).coarsen 32 = tA 16 := by decide +kernel
theorem tA_mem_16 :
    (tA 16).contains (((16 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_16]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_8

theorem tA_eq_17 : dirichletTermBox2 24 5 32 5 10 17 (ptBox (2627 / 125 : ℚ)) = tA 17 := by decide +kernel
theorem tA_mem_17 :
    (tA 17).contains (((17 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_17]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_18 : ((tA 2).mul (tA 9)).coarsen 32 = tA 18 := by decide +kernel
theorem tA_mem_18 :
    (tA 18).contains (((18 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_18]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_9

theorem tA_eq_19 : dirichletTermBox2 24 5 32 5 10 19 (ptBox (2627 / 125 : ℚ)) = tA 19 := by decide +kernel
theorem tA_mem_19 :
    (tA 19).contains (((19 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_19]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_20 : ((tA 2).mul (tA 10)).coarsen 32 = tA 20 := by decide +kernel
theorem tA_mem_20 :
    (tA 20).contains (((20 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_20]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_10

theorem tA_eq_21 : ((tA 3).mul (tA 7)).coarsen 32 = tA 21 := by decide +kernel
theorem tA_mem_21 :
    (tA 21).contains (((21 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_21]
  exact contains_cpow_mul_coarsen 32 tA_mem_3 tA_mem_7

theorem tA_eq_22 : ((tA 2).mul (tA 11)).coarsen 32 = tA 22 := by decide +kernel
theorem tA_mem_22 :
    (tA 22).contains (((22 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_22]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_11

theorem tA_eq_23 : dirichletTermBox2 24 5 32 5 10 23 (ptBox (2627 / 125 : ℚ)) = tA 23 := by decide +kernel
theorem tA_mem_23 :
    (tA 23).contains (((23 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_23]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_24 : ((tA 2).mul (tA 12)).coarsen 32 = tA 24 := by decide +kernel
theorem tA_mem_24 :
    (tA 24).contains (((24 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_24]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_12

theorem tA_eq_25 : ((tA 5).mul (tA 5)).coarsen 32 = tA 25 := by decide +kernel
theorem tA_mem_25 :
    (tA 25).contains (((25 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_25]
  exact contains_cpow_mul_coarsen 32 tA_mem_5 tA_mem_5

theorem tA_eq_26 : ((tA 2).mul (tA 13)).coarsen 32 = tA 26 := by decide +kernel
theorem tA_mem_26 :
    (tA 26).contains (((26 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_26]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_13

theorem tA_eq_27 : ((tA 3).mul (tA 9)).coarsen 32 = tA 27 := by decide +kernel
theorem tA_mem_27 :
    (tA 27).contains (((27 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_27]
  exact contains_cpow_mul_coarsen 32 tA_mem_3 tA_mem_9

theorem tA_eq_28 : ((tA 2).mul (tA 14)).coarsen 32 = tA 28 := by decide +kernel
theorem tA_mem_28 :
    (tA 28).contains (((28 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_28]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_14

theorem tA_eq_29 : dirichletTermBox2 24 5 32 5 10 29 (ptBox (2627 / 125 : ℚ)) = tA 29 := by decide +kernel
theorem tA_mem_29 :
    (tA 29).contains (((29 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_29]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tA_eq_30 : ((tA 2).mul (tA 15)).coarsen 32 = tA 30 := by decide +kernel
theorem tA_mem_30 :
    (tA 30).contains (((30 : ℕ) : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  rw [← tA_eq_30]
  exact contains_cpow_mul_coarsen 32 tA_mem_2 tA_mem_15

theorem tA_mem : ∀ m < 31,
    (tA m).contains ((m : ℂ) ^ (-sOf (((2627 / 125 : ℚ) : ℚ) : ℝ))) := by
  intro m hm
  interval_cases m
  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]
    exact contains_zero
  · exact tA_mem_1
  · exact tA_mem_2
  · exact tA_mem_3
  · exact tA_mem_4
  · exact tA_mem_5
  · exact tA_mem_6
  · exact tA_mem_7
  · exact tA_mem_8
  · exact tA_mem_9
  · exact tA_mem_10
  · exact tA_mem_11
  · exact tA_mem_12
  · exact tA_mem_13
  · exact tA_mem_14
  · exact tA_mem_15
  · exact tA_mem_16
  · exact tA_mem_17
  · exact tA_mem_18
  · exact tA_mem_19
  · exact tA_mem_20
  · exact tA_mem_21
  · exact tA_mem_22
  · exact tA_mem_23
  · exact tA_mem_24
  · exact tA_mem_25
  · exact tA_mem_26
  · exact tA_mem_27
  · exact tA_mem_28
  · exact tA_mem_29
  · exact tA_mem_30

def cA : ComplexInterval := ComplexInterval.exact (9295870901 / 19886501520 : ℚ) (-1700666889593 / 1242906345000 : ℚ)
def epsA : ℚ := (9089 / 10000000 : ℚ)

def tB : ℕ → ComplexInterval
  | 1 => ComplexInterval.exact 1 0
  | 2 => lit (-645470289 / 2147483648 : ℚ) (-645428381 / 2147483648 : ℚ) (-2749033223 / 4294967296 : ℚ) (-1374474747 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 3 => lit (-549582395 / 2147483648 : ℚ) (-1099117341 / 4294967296 : ℚ) (2222768227 / 4294967296 : ℚ) (555703927 / 1073741824 : ℚ) (by decide +kernel) (by decide +kernel)
  | 4 => lit (-85723477 / 268435456 : ℚ) (-685709033 / 2147483648 : ℚ) (1652399097 / 4294967296 : ℚ) (826278361 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 5 => lit (-1453361015 / 4294967296 : ℚ) (-1453267751 / 4294967296 : ℚ) (-1255923233 / 4294967296 : ℚ) (-1255829991 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 6 => lit (438250173 / 1073741824 : ℚ) (1753110127 / 4294967296 : ℚ) (35365825 / 4294967296 : ℚ) (4434409 / 536870912 : ℚ) (by decide +kernel) (by decide +kernel)
  | 7 => lit (-404554105 / 1073741824 : ℚ) (-1618131799 / 4294967296 : ℚ) (64713103 / 2147483648 : ℚ) (129510829 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 8 => lit (1469782075 / 4294967296 : ℚ) (1469989301 / 4294967296 : ℚ) (381052137 / 4294967296 : ℚ) (381259349 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 9 => lit (-434561021 / 2147483648 : ℚ) (-869048609 / 4294967296 : ℚ) (-568861319 / 2147483648 : ℚ) (-568824611 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 10 => lit (-367084097 / 4294967296 : ℚ) (-366943541 / 4294967296 : ℚ) (1307589999 / 4294967296 : ℚ) (1307730559 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 11 => lit (1278447849 / 4294967296 : ℚ) (1278494607 / 4294967296 : ℚ) (-25768943 / 536870912 : ℚ) (-206104777 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 12 => lit (-252148851 / 2147483648 : ℚ) (-31509991 / 268435456 : ℚ) (-1132757043 / 4294967296 : ℚ) (-283154809 / 1073741824 : ℚ) (by decide +kernel) (by decide +kernel)
  | 13 => lit (-1027107313 / 4294967296 : ℚ) (-513482379 / 2147483648 : ℚ) (603400283 / 4294967296 : ℚ) (301771425 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 14 => lit (569169055 / 4294967296 : ℚ) (569282755 / 4294967296 : ℚ) (249185355 / 1073741824 : ℚ) (498427545 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 15 => lit (510915507 / 2147483648 : ℚ) (510966539 / 2147483648 : ℚ) (-215397353 / 2147483648 : ℚ) (-430692635 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 16 => lit (-98973485 / 2147483648 : ℚ) (-197715943 / 4294967296 : ℚ) (-527737731 / 2147483648 : ℚ) (-1055244453 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 17 => lit (-1035422085 / 4294967296 : ℚ) (-1035209423 / 4294967296 : ℚ) (-115105499 / 4294967296 : ℚ) (-14361605 / 536870912 : ℚ) (by decide +kernel) (by decide +kernel)
  | 18 => lit (-467016375 / 4294967296 : ℚ) (-466908175 / 4294967296 : ℚ) (898147217 / 4294967296 : ℚ) (898255429 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 19 => lit (602099239 / 4294967296 : ℚ) (301160865 / 2147483648 : ℚ) (194944095 / 1073741824 : ℚ) (194999715 / 1073741824 : ℚ) (by decide +kernel) (by decide +kernel)
  | 20 => lit (59199671 / 268435456 : ℚ) (947359603 / 4294967296 : ℚ) (-39551709 / 1073741824 : ℚ) (-158041951 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 21 => lit (10845819 / 134217728 : ℚ) (43393871 / 536870912 : ℚ) (-217658853 / 1073741824 : ℚ) (-435275321 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 22 => lit (-64528373 / 536870912 : ℚ) (-129038507 / 1073741824 : ℚ) (-756367205 / 4294967296 : ℚ) (-378147137 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 23 => lit (-895085941 / 4294967296 : ℚ) (-894804573 / 4294967296 : ℚ) (-33400983 / 4294967296 : ℚ) (-258747 / 33554432 : ℚ) (by decide +kernel) (by decide +kernel)
  | 24 => lit (-71688223 / 536870912 : ℚ) (-143336057 / 1073741824 : ℚ) (663092169 / 4294967296 : ℚ) (663253751 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 25 => lit (3890047 / 134217728 : ℚ) (62299575 / 2147483648 : ℚ) (849858497 / 4294967296 : ℚ) (424988071 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 26 => lit (173713855 / 1073741824 : ℚ) (173755331 / 1073741824 : ℚ) (475891003 / 4294967296 : ℚ) (476056895 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 27 => lit (811162623 / 4294967296 : ℚ) (405620795 / 2147483648 : ℚ) (-158671323 / 4294967296 : ℚ) (-158592353 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 28 => lit (233422221 / 2147483648 : ℚ) (58372739 / 536870912 : ℚ) (-663999909 / 4294967296 : ℚ) (-663862421 / 4294967296 : ℚ) (by decide +kernel) (by decide +kernel)
  | 29 => lit (-99662215 / 4294967296 : ℚ) (-99232541 / 4294967296 : ℚ) (-791546583 / 4294967296 : ℚ) (-395558455 / 2147483648 : ℚ) (by decide +kernel) (by decide +kernel)
  | 30 => lit (-582897067 / 4294967296 : ℚ) (-36423295 / 268435456 : ℚ) (-65581567 / 536870912 : ℚ) (-131132051 / 1073741824 : ℚ) (by decide +kernel) (by decide +kernel)
  | _ => ComplexInterval.exact 0 0

theorem tB_mem_1 :
    (tB 1).contains (((1 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := contains_one_cpow _

theorem tB_eq_2 : dirichletTermBox2 24 5 32 2 10 2 (ptBox (21029 / 1000 : ℚ)) = tB 2 := by decide +kernel
theorem tB_mem_2 :
    (tB 2).contains (((2 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_2]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_3 : dirichletTermBox2 24 5 32 2 10 3 (ptBox (21029 / 1000 : ℚ)) = tB 3 := by decide +kernel
theorem tB_mem_3 :
    (tB 3).contains (((3 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_3]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_4 : ((tB 2).mul (tB 2)).coarsen 32 = tB 4 := by decide +kernel
theorem tB_mem_4 :
    (tB 4).contains (((4 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_4]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_2

theorem tB_eq_5 : dirichletTermBox2 24 5 32 3 10 5 (ptBox (21029 / 1000 : ℚ)) = tB 5 := by decide +kernel
theorem tB_mem_5 :
    (tB 5).contains (((5 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_5]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_6 : ((tB 2).mul (tB 3)).coarsen 32 = tB 6 := by decide +kernel
theorem tB_mem_6 :
    (tB 6).contains (((6 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_6]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_3

theorem tB_eq_7 : dirichletTermBox2 24 5 32 3 10 7 (ptBox (21029 / 1000 : ℚ)) = tB 7 := by decide +kernel
theorem tB_mem_7 :
    (tB 7).contains (((7 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_7]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_8 : ((tB 2).mul (tB 4)).coarsen 32 = tB 8 := by decide +kernel
theorem tB_mem_8 :
    (tB 8).contains (((8 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_8]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_4

theorem tB_eq_9 : ((tB 3).mul (tB 3)).coarsen 32 = tB 9 := by decide +kernel
theorem tB_mem_9 :
    (tB 9).contains (((9 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_9]
  exact contains_cpow_mul_coarsen 32 tB_mem_3 tB_mem_3

theorem tB_eq_10 : ((tB 2).mul (tB 5)).coarsen 32 = tB 10 := by decide +kernel
theorem tB_mem_10 :
    (tB 10).contains (((10 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_10]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_5

theorem tB_eq_11 : dirichletTermBox2 24 5 32 4 10 11 (ptBox (21029 / 1000 : ℚ)) = tB 11 := by decide +kernel
theorem tB_mem_11 :
    (tB 11).contains (((11 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_11]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_12 : ((tB 2).mul (tB 6)).coarsen 32 = tB 12 := by decide +kernel
theorem tB_mem_12 :
    (tB 12).contains (((12 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_12]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_6

theorem tB_eq_13 : dirichletTermBox2 24 5 32 4 10 13 (ptBox (21029 / 1000 : ℚ)) = tB 13 := by decide +kernel
theorem tB_mem_13 :
    (tB 13).contains (((13 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_13]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_14 : ((tB 2).mul (tB 7)).coarsen 32 = tB 14 := by decide +kernel
theorem tB_mem_14 :
    (tB 14).contains (((14 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_14]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_7

theorem tB_eq_15 : ((tB 3).mul (tB 5)).coarsen 32 = tB 15 := by decide +kernel
theorem tB_mem_15 :
    (tB 15).contains (((15 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_15]
  exact contains_cpow_mul_coarsen 32 tB_mem_3 tB_mem_5

theorem tB_eq_16 : ((tB 2).mul (tB 8)).coarsen 32 = tB 16 := by decide +kernel
theorem tB_mem_16 :
    (tB 16).contains (((16 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_16]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_8

theorem tB_eq_17 : dirichletTermBox2 24 5 32 5 10 17 (ptBox (21029 / 1000 : ℚ)) = tB 17 := by decide +kernel
theorem tB_mem_17 :
    (tB 17).contains (((17 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_17]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_18 : ((tB 2).mul (tB 9)).coarsen 32 = tB 18 := by decide +kernel
theorem tB_mem_18 :
    (tB 18).contains (((18 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_18]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_9

theorem tB_eq_19 : dirichletTermBox2 24 5 32 5 10 19 (ptBox (21029 / 1000 : ℚ)) = tB 19 := by decide +kernel
theorem tB_mem_19 :
    (tB 19).contains (((19 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_19]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_20 : ((tB 2).mul (tB 10)).coarsen 32 = tB 20 := by decide +kernel
theorem tB_mem_20 :
    (tB 20).contains (((20 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_20]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_10

theorem tB_eq_21 : ((tB 3).mul (tB 7)).coarsen 32 = tB 21 := by decide +kernel
theorem tB_mem_21 :
    (tB 21).contains (((21 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_21]
  exact contains_cpow_mul_coarsen 32 tB_mem_3 tB_mem_7

theorem tB_eq_22 : ((tB 2).mul (tB 11)).coarsen 32 = tB 22 := by decide +kernel
theorem tB_mem_22 :
    (tB 22).contains (((22 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_22]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_11

theorem tB_eq_23 : dirichletTermBox2 24 5 32 5 10 23 (ptBox (21029 / 1000 : ℚ)) = tB 23 := by decide +kernel
theorem tB_mem_23 :
    (tB 23).contains (((23 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_23]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_24 : ((tB 2).mul (tB 12)).coarsen 32 = tB 24 := by decide +kernel
theorem tB_mem_24 :
    (tB 24).contains (((24 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_24]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_12

theorem tB_eq_25 : ((tB 5).mul (tB 5)).coarsen 32 = tB 25 := by decide +kernel
theorem tB_mem_25 :
    (tB 25).contains (((25 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_25]
  exact contains_cpow_mul_coarsen 32 tB_mem_5 tB_mem_5

theorem tB_eq_26 : ((tB 2).mul (tB 13)).coarsen 32 = tB 26 := by decide +kernel
theorem tB_mem_26 :
    (tB 26).contains (((26 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_26]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_13

theorem tB_eq_27 : ((tB 3).mul (tB 9)).coarsen 32 = tB 27 := by decide +kernel
theorem tB_mem_27 :
    (tB 27).contains (((27 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_27]
  exact contains_cpow_mul_coarsen 32 tB_mem_3 tB_mem_9

theorem tB_eq_28 : ((tB 2).mul (tB 14)).coarsen 32 = tB 28 := by decide +kernel
theorem tB_mem_28 :
    (tB 28).contains (((28 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_28]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_14

theorem tB_eq_29 : dirichletTermBox2 24 5 32 5 10 29 (ptBox (21029 / 1000 : ℚ)) = tB 29 := by decide +kernel
theorem tB_mem_29 :
    (tB 29).contains (((29 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_29]
  exact contains_dirichletTermBox2 (by norm_num) (by norm_num) (by norm_num)
    (ptBox_contains _) (by norm_num) (by norm_num) (by decide +kernel)

theorem tB_eq_30 : ((tB 2).mul (tB 15)).coarsen 32 = tB 30 := by decide +kernel
theorem tB_mem_30 :
    (tB 30).contains (((30 : ℕ) : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  rw [← tB_eq_30]
  exact contains_cpow_mul_coarsen 32 tB_mem_2 tB_mem_15

theorem tB_mem : ∀ m < 31,
    (tB m).contains ((m : ℂ) ^ (-sOf (((21029 / 1000 : ℚ) : ℚ) : ℝ))) := by
  intro m hm
  interval_cases m
  · rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr (sOf_ne_zero _))]
    exact contains_zero
  · exact tB_mem_1
  · exact tB_mem_2
  · exact tB_mem_3
  · exact tB_mem_4
  · exact tB_mem_5
  · exact tB_mem_6
  · exact tB_mem_7
  · exact tB_mem_8
  · exact tB_mem_9
  · exact tB_mem_10
  · exact tB_mem_11
  · exact tB_mem_12
  · exact tB_mem_13
  · exact tB_mem_14
  · exact tB_mem_15
  · exact tB_mem_16
  · exact tB_mem_17
  · exact tB_mem_18
  · exact tB_mem_19
  · exact tB_mem_20
  · exact tB_mem_21
  · exact tB_mem_22
  · exact tB_mem_23
  · exact tB_mem_24
  · exact tB_mem_25
  · exact tB_mem_26
  · exact tB_mem_27
  · exact tB_mem_28
  · exact tB_mem_29
  · exact tB_mem_30

def cB : ComplexInterval := ComplexInterval.exact (148931251601 / 318577565520 : ℚ) (-217808522742611 / 159288782760000 : ℚ)
def epsB : ℚ := (911 / 1000000 : ℚ)

end HardySecondInterval

end

section
open Complex Finset ZetaLean ZetaLean.ComplexInterval
open scoped ComplexConjugate

open HardyFirstZero

namespace HardySecondInterval

set_option maxRecDepth 100000

/-- The rectangle for the order-4 main term at `t = 2627/125`. -/
def MA : ComplexInterval := (sumBoxes tA 30).add ((tA 30).mul cA)

/-- The rectangle for the order-4 main term at `t = 21029/1000`. -/
def MB : ComplexInterval := (sumBoxes tB 30).add ((tB 30).mul cB)

lemma cA_mem : cA.contains (((30 : ℕ) : ℂ) / (sOf ((2627 / 125 : ℚ) : ℝ) - 1) + 1 / 2
    + sOf ((2627 / 125 : ℚ) : ℝ) / (12 * ((30 : ℕ) : ℂ))) := by
  have h := contains_exact (9295870901 / 19886501520 : ℚ) (-1700666889593 / 1242906345000 : ℚ)
  unfold cA
  convert h using 1
  apply Complex.ext <;>
    simp [sOf, Complex.div_re, Complex.div_im, Complex.normSq] <;> norm_num

lemma cB_mem : cB.contains (((30 : ℕ) : ℂ) / (sOf ((21029 / 1000 : ℚ) : ℝ) - 1) + 1 / 2
    + sOf ((21029 / 1000 : ℚ) : ℝ) / (12 * ((30 : ℕ) : ℂ))) := by
  have h := contains_exact (148931251601 / 318577565520 : ℚ) (-217808522742611 / 159288782760000 : ℚ)
  unfold cB
  convert h using 1
  apply Complex.ext <;>
    simp [sOf, Complex.div_re, Complex.div_im, Complex.normSq] <;> norm_num

/-- `ζ(1/2 + 21.016i)` lies in `MA` inflated by `epsA`. -/
theorem zetaA_mem : (MA.inflate epsA).contains (riemannZeta (sOf ((2627 / 125 : ℚ) : ℝ))) := by
  set s := sOf ((2627 / 125 : ℚ) : ℝ)
  have hM : MA.contains (∑ i ∈ range 30, (i : ℂ) ^ (-s) + ((30 : ℕ) : ℂ) ^ (1 - s) / (s - 1)
      + ((30 : ℕ) : ℂ) ^ (-s) / 2 + s / 12 * ((30 : ℕ) : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by norm_num)]
    exact contains_add (contains_sumBoxes fun m hm => tA_mem m (by omega))
      (contains_mul (tA_mem 30 (by norm_num)) cA_mem)
  refine contains_inflate hM ((em30_bound (T := 2627 / 125) (by norm_num) (by norm_num)).trans ?_)
  simp only [epsA]
  norm_num

/-- `ζ(1/2 + 21.029i)` lies in `MB` inflated by `epsB`. -/
theorem zetaB_mem : (MB.inflate epsB).contains (riemannZeta (sOf ((21029 / 1000 : ℚ) : ℝ))) := by
  set s := sOf ((21029 / 1000 : ℚ) : ℝ)
  have hM : MB.contains (∑ i ∈ range 30, (i : ℂ) ^ (-s) + ((30 : ℕ) : ℂ) ^ (1 - s) / (s - 1)
      + ((30 : ℕ) : ℂ) ^ (-s) / 2 + s / 12 * ((30 : ℕ) : ℂ) ^ (-s - 1)) := by
    rw [main_eq s (by norm_num)]
    exact contains_add (contains_sumBoxes fun m hm => tB_mem m (by omega))
      (contains_mul (tB_mem 30 (by norm_num)) cB_mem)
  refine contains_inflate hM ((em30_bound (T := 21029 / 1000) (by norm_num) (by norm_num)).trans ?_)
  simp only [epsB]
  norm_num

/-- The interval product decides the sign: its upper end is negative. -/
theorem product_hi_neg :
    (((MA.inflate epsA).re.mul (MB.inflate epsB).re).add
      ((MA.inflate epsA).im.mul (MB.inflate epsB).im)).hi < 0 := by
  decide +kernel

/-- **`hX` at the planned endpoints**: `Re(ζ(1/2 + 21.016i) · conj ζ(1/2 + 21.029i)) < 0`. -/
theorem zeta_product_re_neg :
    (riemannZeta (sOf (2627 / 125)) * conj (riemannZeta (sOf (21029 / 1000)))).re < 0 := by
  have ha : ((2627 / 125 : ℚ) : ℝ) = 2627 / 125 := by norm_num
  have hb : ((21029 / 1000 : ℚ) : ℝ) = 21029 / 1000 := by norm_num
  have hA := zetaA_mem
  have hB := zetaB_mem
  rw [ha] at hA
  rw [hb] at hB
  set z := riemannZeta (sOf (2627 / 125))
  set w := riemannZeta (sOf (21029 / 1000))
  have hre : (z * conj w).re = z.re * w.re + z.im * w.im := by
    simp [Complex.mul_re]
  have hc := Interval.contains_add (Interval.contains_mul hA.1 hB.1)
    (Interval.contains_mul hA.2 hB.2)
  rw [hre]
  have hneg : ((((MA.inflate epsA).re.mul (MB.inflate epsB).re).add
      ((MA.inflate epsA).im.mul (MB.inflate epsB).im)).hi : ℝ) < 0 := by
    exact_mod_cast product_hi_neg
  exact lt_of_le_of_lt hc.2 hneg

end HardySecondInterval

theorem XiQuantitativePublished.zeta_zero_between_21016_21029 :
    ∃ t ∈ Set.Ioo (2627 / 125 : ℝ) (21029 / 1000),
      riemannZeta (1 / 2 + t * Complex.I) = 0 :=
  HardyFirstZero.exists_zero_of_sign_data (by norm_num)
    HardySecondInterval.zeta_product_re_neg HardyFirstZero.gammaR_re_pos_second
end

section
/- The multiplicity, kernel comparison and reflected pair construction are adapted
   from marozols' solution 5cd760ea-f5f1-43db-b84d-4666e82126c5. The
   multiplicity argument is due to Yi. -/
open Set
namespace MasulloRH

-- Positivity argument from Yi's proof of MasulloRH.single_resolvent_test.
private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem one_ordinate_bound (z : ZetaZerosInTraceStrip (1/2))
    (hl : (2627/125:ℝ)^2 ≤ z.val.im^2) (hu : z.val.im^2 ≤ (21029/1000:ℝ)^2) :
    27/25000 ≤ (analyticOrderNatAt riemannZeta z.val:ℝ) *
      ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))) := by
  let Y := z.val.im^2
  have hy0 : 0 ≤ Y := sq_nonneg _
  have hnum : (2627/125:ℝ)^2-5 ≤ Y-5 := sub_le_sub_right hl 5
  have hden : 2*(Y+25/4)*(Y+4) ≤ 2*((21029/1000:ℝ)^2+25/4)*((21029/1000:ℝ)^2+4) :=
    mul_le_mul (by linarith only [hu]) (by linarith only [hu]) (by positivity) (by norm_num)
  have hval : 27/25000 ≤ (Y-5)/(2*(Y+25/4)*(Y+4)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [hden,hnum]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact hval.trans (le_mul_of_one_le_left (by linarith) hm)

private theorem secondPairMass
    (hzero : ∃ t ∈ Set.Ioo (2627 / 125 : ℝ) (21029 / 1000),
      riemannZeta (1/2 + t * Complex.I) = 0) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), F.card = 2 ∧
      (∀ z ∈ F, z.val.re = 1/2 ∧ 2627/125 < |z.val.im| ∧ |z.val.im| < 21029/1000) ∧
      27/12500 ≤ ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))) := by
  classical
  obtain ⟨t,ht,hz⟩ := hzero
  have ht0 : 0 < t := by linarith [ht.1]
  let u : ℂ := 1/2+(t:ℂ)*Complex.I
  have hur : u.re = 1/2 := by norm_num [u,Complex.add_re,Complex.mul_re,Complex.div_ofNat_re]
  have hui : u.im = t := by norm_num [u,Complex.add_im,Complex.mul_im,Complex.div_ofNat_im]
  have hvr : (1-u).re = 1/2 := by rw [Complex.sub_re,Complex.one_re,hur]; ring
  have hvi : (1-u).im = -t := by simp [Complex.sub_im,hui]
  have hnot (n : ℕ) : u ≠ -n := by
    intro h; have he := congrArg Complex.re h; simp [hur] at he; linarith [n.cast_nonneg (α:=ℝ)]
  have h1 : u ≠ 1 := by intro h; have he := congrArg Complex.re h; norm_num [hur] at he
  have hz' : riemannZeta (1-u) = 0 := by rw [riemannZeta_one_sub hnot h1,show riemannZeta u = 0 from hz,mul_zero]
  let a : ZetaZerosInTraceStrip (1/2) := ⟨u,hz,by norm_num [hur],by norm_num [hur],by norm_num [hur]⟩
  let b : ZetaZerosInTraceStrip (1/2) := ⟨1-u,hz',by norm_num [hvr],by norm_num [hvr],by norm_num [hvr]⟩
  have hab : a ≠ b := by
    intro h; have he := congrArg (fun z : ZetaZerosInTraceStrip (1/2) => z.val.im) h
    change u.im = (1-u).im at he; rw [hui,hvi] at he; linarith
  have hL : (2627/125:ℝ)^2 ≤ t^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤2627/125) ht.1.le]
  have hU : t^2 ≤ (21029/1000:ℝ)^2 := by nlinarith [mul_self_le_mul_self ht0.le ht.2.le]
  have ha := one_ordinate_bound a (by simpa [a,hui] using hL) (by simpa [a,hui] using hU)
  have hb := one_ordinate_bound b (by simpa [b,hvi] using hL) (by simpa [b,hvi] using hU)
  refine ⟨{a,b}, by simp [hab], ?_, ?_⟩
  · intro z hzF
    rcases Finset.mem_insert.mp hzF with rfl | hzF
    · simpa [a,hur,hui,abs_of_pos ht0] using ht
    · obtain rfl := Finset.mem_singleton.mp hzF
      simpa [b,hvr,hvi,abs_of_pos ht0] using ht
  · rw [Finset.sum_pair hab]
    linarith only [ha,hb]

end MasulloRH
end

section
/-!
# Finite prime side of the two-pair critical-line mass certificate

Adapted from marozols' accepted proof of `MasulloRH.critical_line_mass_first_pair_certificate`
on Prove2Me. The original rational majorants and comparison lemma cover the range through 8.
At 9 the von Mangoldt weight is `log 3`; at 10 it vanishes. The same rational estimates
then give the upper bound `63/10000` for every prefix of the range through 10.

Source theorem: https://prove2.me/theorems/6a993fae-e7d3-461e-a029-f2eb21fc3914
Accepted Lean source: https://prove2.me/api/v1/submissions/5cd760ea-f5f1-43db-b84d-4666e82126c5/solution
-/

open ArithmeticFunction

namespace MasulloRH

private theorem prime_term_bound {n : ℕ} {l U : ℝ} (hn : 1 ≤ n) (hl : 0 < l)
    (hsq : l^2 ≤ n) (hU : vonMangoldt n ≤ U) :
    vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ) ≤
      U*(1/((n:ℝ)^2*l)-1/(n:ℝ)^3) := by
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hL : l ≤ Real.sqrt (n:ℝ) := (Real.le_sqrt hl.le (by positivity)).mpr hsq
  have hroot : Real.sqrt (n:ℝ) ≤ n := by
    apply (Real.sqrt_le_iff.mpr ⟨hn0.le,?_⟩)
    nlinarith [mul_nonneg hn0.le (show 0 ≤ (n:ℝ)-1 by linarith)]
  have hp := Real.rpow_add hn0 (2:ℝ) (1/2:ℝ)
  rw [show (2:ℝ)+1/2 = 5/2 by norm_num, Real.rpow_two, ← Real.sqrt_eq_rpow] at hp
  rw [hp,Real.rpow_ofNat]
  have hc : 0 ≤ 1 / ((n:ℝ)^2*Real.sqrt (n:ℝ)) - 1/(n:ℝ)^3 := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    simpa [pow_succ] using mul_le_mul_of_nonneg_left hroot (sq_nonneg (n:ℝ))
  have hK : 1/((n:ℝ)^2*Real.sqrt n) ≤ 1/((n:ℝ)^2*l) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hL (sq_nonneg _))
  calc _ = vonMangoldt n * (1 / ((n:ℝ)^2*Real.sqrt (n:ℝ)) - 1/(n:ℝ)^3) := by ring
       _ ≤ U*(1 / ((n:ℝ)^2*l)-1/(n:ℝ)^3) :=
         mul_le_mul hU (sub_le_sub_right hK _) hc (vonMangoldt_nonneg.trans hU)

/-- The range excludes its upper endpoint, so only the indices through 10 occur. -/
theorem prime_trace_sum_le_63_10000 {N : ℕ} (hN : N ≤ 11) :
    Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤
    63/10000 := by
  let f (n : ℕ) := vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ)
  have hpos (n : ℕ) : 0 ≤ f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
    (fun n _ _ => hpos n)
  change _ + (∑ n ∈ Finset.range N, f n) ≤ _
  apply (add_le_add_right hle _).trans
  have h2 : vonMangoldt 2 ≤ (694/1000:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide)]; linarith [Real.log_two_lt_d9]
  have h3 : vonMangoldt 3 ≤ (1099/1000:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide)]; linarith [Real.log_three_lt_d9]
  have h4 : vonMangoldt 4 ≤ (694/1000:ℝ) := by
    change vonMangoldt (2^2) ≤ _; rwa [vonMangoldt_apply_pow (by decide)]
  have h5 : vonMangoldt 5 ≤ (161/100:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide)]; linarith [Real.log_five_lt_d9]
  have h6 : vonMangoldt 6 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
  have h7 : vonMangoldt 7 ≤ (2:ℝ) := by
    rw [vonMangoldt_apply_prime (by decide),Real.log_le_iff_le_exp (by norm_num),
      show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    have hL : (2.7:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact (show (7:ℝ) ≤ 2.7*2.7 by norm_num).trans
      (mul_le_mul hL hL (by norm_num) (Real.exp_pos _).le)
  have h8 : vonMangoldt 8 ≤ (694/1000:ℝ) := by
    change vonMangoldt (2^3) ≤ _; rwa [vonMangoldt_apply_pow (by decide)]
  have h9 : vonMangoldt 9 ≤ (1099/1000:ℝ) := by
    change vonMangoldt (3^2) ≤ _; rwa [vonMangoldt_apply_pow (by decide)]
  have h10 : vonMangoldt 10 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
  have b2 := prime_term_bound (n:=2) (l:=1.414) (by decide) (by norm_num) (by norm_num) h2
  have b3 := prime_term_bound (n:=3) (l:=1.732) (by decide) (by norm_num) (by norm_num) h3
  have b4 := prime_term_bound (n:=4) (l:=2) (by decide) (by norm_num) (by norm_num) h4
  have b5 := prime_term_bound (n:=5) (l:=2.236) (by decide) (by norm_num) (by norm_num) h5
  have b7 := prime_term_bound (n:=7) (l:=2.645) (by decide) (by norm_num) (by norm_num) h7
  have b8 := prime_term_bound (n:=8) (l:=2.828) (by decide) (by norm_num) (by norm_num) h8
  have b9 := prime_term_bound (n:=9) (l:=3) (by decide) (by norm_num) (by norm_num) h9
  simp only [Finset.sum_range_succ,Finset.sum_range_zero] at *
  norm_num [f,h6,h10] at b2 b3 b4 b5 b7 b8 b9 ⊢
  linarith only [b2,b3,b4,b5,b7,b8,b9,Real.pi_lt_d4,Real.log_two_lt_d9]

/-- The requested comparison threshold for the two-pair certificate. -/
theorem prime_trace_sum_le_67_10000 {N : ℕ} (hN : N ≤ 11) :
    Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) - vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤
    67/10000 :=
  (prime_trace_sum_le_63_10000 hN).trans (by norm_num)

end MasulloRH
end

open MasulloRH ArithmeticFunction

open scoped Classical

theorem solution :
    ∃ A B : Finset (ZetaZerosInTraceStrip (1/2)), A.card = 2 ∧ B.card = 2 ∧ Disjoint A B ∧
      (∀ z ∈ A, z.val.re = 1/2 ∧ 1413/100 < |z.val.im| ∧ |z.val.im| < 707/50) ∧
      (∀ z ∈ B, z.val.re = 1/2 ∧ 2627/125 < |z.val.im| ∧ |z.val.im| < 21029/1000) ∧
      169/25000 ≤ (∑ z ∈ A ∪ B, (analyticOrderNatAt riemannZeta z.val : ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) ∧
      ∀ N : ℕ, N ≤ 11 → Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤ 63/10000 := by
  classical
  obtain ⟨A, hA, hlocA, hmA, _⟩ := MasulloRH.critical_line_mass_first_pair_certificate
  obtain ⟨B, hB, hlocB, hmB⟩ := MasulloRH.secondPairMass
    XiQuantitativePublished.zeta_zero_between_21016_21029
  have hd : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro z hza hzb
    linarith [(hlocA z hza).2.2, (hlocB z hzb).2.1]
  refine ⟨A, B, hA, hB, hd, hlocA, hlocB, ?_, fun _ hN => MasulloRH.prime_trace_sum_le_63_10000 hN⟩
  rw [Finset.sum_union hd]
  linarith only [hmA, hmB]
